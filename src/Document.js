const {process} = global;

const parse5 = require('parse5');

const DOM = require('./DOM');
const {Event, EventTarget} = require('./Event');
const GlobalContext = require('./GlobalContext');
const nativeBindings = require('./native-bindings');
const symbols = require('./symbols');
const utils = require('./utils');

const _parseDocument = (s, window) => {
  const ast = parse5.parse(s, {
    sourceCodeLocationInfo: true,
  });
  ast.tagName = 'document';
  return _parseDocumentAst(ast, window, true);
};
module.exports._parseDocument = _parseDocument;
GlobalContext._parseDocument = _parseDocument;

const _parseDocumentAst = (ast, window, uppercase) => {
  const document = _fromAST(ast, window, null, null, uppercase);
  return initDocument(document, window);
};
module.exports._parseDocumentAst = _parseDocumentAst;

/**
 * Initialize document instance with properties and methods.
 */
function initDocument (document, window) {
  const html = document.childNodes.find(el => el.tagName === 'HTML');
  const documentElement = html || (document.childNodes.length > 0 ? document.childNodes[0] : null);
  const head = html ? html.childNodes.find(el => el.tagName === 'HEAD') : null;
  const body = html ? html.childNodes.find(el => el.tagName === 'BODY') : null;

  document.documentElement = documentElement;
  document.readyState = 'loading';
  document.head = head;
  document.body = body;
  document.location = window.location;
  document.cookie = '';
  document.createElement = tagName => {
    tagName = tagName.toUpperCase();
    const HTMLElementTemplate = window[symbols.htmlTagsSymbol][tagName];
    const element = HTMLElementTemplate ? new HTMLElementTemplate() : new DOM.HTMLElement(tagName);
    element.ownerDocument = document;
    return element;
  };
  document.createElementNS = (namespace, tagName) => document.createElement(tagName);
  document.createDocumentFragment = () => {
    const documentFragment = new DocumentFragment();
    documentFragment.ownerDocument = document;
    return documentFragment;
  };
  document.createRange = () => {
    const range = new Range();
    range.ownerDocument = document;
    return range;
  };
  document.createTextNode = text => {
    const node = new DOM.Text(text);
    node.ownerDocument = document;
    return node;
  }
  document.createComment = comment => {
    const node = new DOM.Comment(comment);
    node.ownerDocument = document;
    return node;
  };
  document.createEvent = type => {
    switch (type) {
      case 'KeyboardEvent':
      case 'KeyboardEvents':
        return new KeyboardEvent();
      case 'MouseEvent':
      case 'MouseEvents':
        return new MouseEvent();
      case 'Event':
      case 'Events':
      case 'HTMLEvents':
        return new Event();
      default:
        throw new Error('invalid createEvent type: ' + type);
    }
  };
  document.importNode = (el, deep) => el.cloneNode(deep);
  document.scripts = utils._makeHtmlCollectionProxy(document.documentElement, 'script');
  document.styleSheets = [];
  document.implementation = new DOMImplementation(window);
  document.resources = new GlobalContext.Resources(); // non-standard
  document.activeElement = body;
  document.open = () => {
    document.innerHTML = '';
  };
  document.close = () => {};
  document.write = htmlString => {
    const childNodes = parse5.parseFragment(htmlString, {
      locationInfo: true,
    }).childNodes.map(childNode => _fromAST(childNode, window, document.body, document, true));
    for (let i = 0; i < childNodes.length; i++) {
      document.body.appendChild(childNodes[i]);
    }
  };
  document.execCommand = command => {
    if (command === 'copy') {
      // nothing
    } else if (command === 'paste') {
      document.dispatchEvent(new Event('paste'));
    }
  };
  document[symbols.pointerLockElementSymbol] = null;
  document[symbols.fullscreenElementSymbol] = null;

  const runElQueue = [];
  const _addRun = fn => {
    (async () => {
      if (!document[symbols.runningSymbol]) {
        document[symbols.runningSymbol] = true;

        try {
          await fn();
        } catch(err) {
          console.warn(err.stack);
        }

        document[symbols.runningSymbol] = false;
        if (runElQueue.length > 0) {
          _addRun(runElQueue.shift());
        } else {
          document.emit('flush');
        }
      } else {
        runElQueue.push(fn);
      }
    })();
  };
  document[symbols.runningSymbol] = false;
  document[symbols.addRunSymbol] = _addRun;

  if (window.top === window) {
    document.addEventListener('pointerlockchange', () => {
      const pointerLockElement = document[symbols.pointerLockElementSymbol];
      
      for (let i = 0; i < GlobalContext.contexts.length; i++) {
        const context = GlobalContext.contexts[i];
        const windowHandle = context.getWindowHandle();
        const argsBuffer = new Uint32Array(2 + 1);
        let index = 0;
        argsBuffer[index++] = windowHandle[0];
        argsBuffer[index++] = windowHandle[1];
        argsBuffer[index++] = pointerLockElement ? 0 : 1;
        global.runSyncTop(nativeBindings.nativeWindow.setCursorMode.functionAddress, argsBuffer);
        /* global.runSyncTop(`(() => {
          const {
            windowHandles,
            pointerLockElement,
          } = global._;
          for (let i = 0; i < windowHandles.length; i++) {
            const windowHandle = windowHandles[i];

            if (nativeBindings.nativeWindow.isVisible(windowHandle)) {
              // console.log('set cursor mode', windowHandle, (windowHandle[0]<<32)|windowHandle[1], !pointerLockElement);
              nativeBindings.nativeWindow.setCursorMode(windowHandle, !pointerLockElement);
            }
          }
        })()`, {
          windowHandles,
          pointerLockElement,
        }); */
      }

      const iframes = document.getElementsByTagName('iframe');
      for (let i = 0; i < iframes.length; i++) {
        const iframe = iframes[i];
        if (iframe.contentDocument) {
          // iframe.contentDocument._emit('pointerlockchange'); // XXX send this down
        }
      }
    });
    document.addEventListener('fullscreenchange', () => {
      const fullscreenElement = document[symbols.fullscreenElementSymbol];
      
      for (let i = 0; i < GlobalContext.contexts.length; i++) {
        const context = GlobalContext.contexts[i];
        const windowHandle = context.getWindowHandle();
        const argsBuffer = new Uint32Array(2 + 1);
        let index = 0;
        argsBuffer[index++] = windowHandle[0];
        argsBuffer[index++] = windowHandle[1];
        argsBuffer[index++] = fullscreenElement ? 1 : 0;
        global.runSyncTop(nativeBindings.setFullscreen.setCursorMode.functionAddress, argsBuffer);
      
        /* global.runSyncTop(`(() => {
          const {
            windowHandles,
            fullscreenElement,
          } = global._;
          for (let i = 0; i < windowHandles.length; i++) {
            const windowHandle = windowHandles[i];

            if (nativeBindings.nativeWindow.isVisible(windowHandle)) {
              if (fullscreenElement) {
                nativeBindings.nativeWindow.setFullscreen(windowHandle);
              } else {
                nativeBindings.nativeWindow.exitFullscreen(windowHandle);
              }
            }
          }
        })()`, {
          windowHandles,
          fullscreenElement,
        }); */
      }
      
      const iframes = document.getElementsByTagName('iframe');
      for (let i = 0; i < iframes.length; i++) {
        const iframe = iframes[i];
        if (iframe.contentDocument) {
          // iframe.contentDocument._emit('pointerlockchange'); // XXX send this down
          iframe.contentDocument._emit('fullscreenchange');
        }
      }
    });
  }

  process.nextTick(async () => {
    if (body) {
      const bodyChildNodes = body.childNodes;
      body.childNodes = new DOM.NodeList();

      try {
        await GlobalContext._runHtml(document.head, window);
      } catch(err) {
        console.warn(err);
      }

      body.childNodes = bodyChildNodes;

      document.dispatchEvent(new Event('DOMContentLoaded', {target: document}));

      try {
        await GlobalContext._runHtml(document.body, window);
      } catch(err) {
        console.warn(err);
      }
    } else {
      try {
        await GlobalContext._runHtml(document, window);
      } catch(err) {
        console.warn(err);
      }

      document.dispatchEvent(new Event('DOMContentLoaded', {target: document}));
    }

    document.readyState = 'interactive';
    document.dispatchEvent(new Event('readystatechange', {target: document}));

    document.readyState = 'complete';
    document.dispatchEvent(new Event('readystatechange', {target: document}));

    document.dispatchEvent(new Event('load', {target: document}));
    window.dispatchEvent(new Event('load', {target: window}));

    const displays = window.navigator.getVRDisplaysSync();
    if (displays.length > 0 && (!window[symbols.optionsSymbol].args || ['all', 'webvr'].includes(window[symbols.optionsSymbol].args.xr))) {
      const _initDisplays = () => {
        if (!_tryEmitDisplay()) {
          _delayFrames(() => {
            _tryEmitDisplay();
          }, 1);
        }
      };
      const _tryEmitDisplay = () => {
        const presentingDisplay = displays.find(display => display.isPresenting);
        if (presentingDisplay) {
          if (presentingDisplay.constructor.name === 'FakeVRDisplay') {
            _emitOneDisplay(presentingDisplay);
          }
          return true;
        } else {
          _emitOneDisplay(displays[0]);
          return false;
        }
      };
      const _emitOneDisplay = display => {
        const e = new window.Event('vrdisplayactivate');
        e.display = display;
        window.dispatchEvent(e);
      };
      const _delayFrames = (fn, n = 1) => {
        if (n === 0) {
          fn();
        } else {
          try {
            window.requestAnimationFrame(() => {
              _delayFrames(fn, n - 1);
            });
          } catch(err) {
            console.log(err.stack);
          }
        }
      };
      if (document.resources.resources.length === 0) {
        _initDisplays();
      } else {
        const _update = () => {
          if (document.resources.resources.length === 0) {
            _initDisplays();
            document.resources.removeEventListener('update', _update);
          }
        };
        document.resources.addEventListener('update', _update);
      }
    }
  });

  return document;
}
module.exports.initDocument = initDocument;

const maxParallelResources = 8;
class Resource {
  constructor(getCb = (onprogress, cb) => cb(), value = 0.5, total = 1) {
    this.getCb = getCb;
    this.value = value;
    this.total = total;
    
    this.onupdate = null;
  }

  setProgress(value) {
    this.value = value;

    this.onupdate && this.onupdate();
  }
  
  get() {
    return new Promise((accept, reject) => {
      this.getCb(progress => {
        this.setValue(progress);
      }, err => {
        if (!err) {
          accept();
        } else {
          reject(err);
        }
      });
    });
  }
  
  destroy() {
    this.setProgress(1);
  }
}
class Resources extends EventTarget {
  constructor() {
    super();
    
    this.resources = [];
    this.queue = [];
    this.numRunning = 0;
  }

  getValue() {
    let value = 0;
    for (let i = 0; i < this.resources.length; i++) {
      value += this.resources[i].value;
    }
    return value;
  }
  getTotal() {
    let total = 0;
    for (let i = 0; i < this.resources.length; i++) {
      total += this.resources[i].total;
    }
    return total;
  }
  getProgress() {
    let value = 0;
    let total = 0;
    for (let i = 0; i < this.resources.length; i++) {
      const resource = this.resources[i];
      value += resource.value;
      total += resource.total;
    }
    return total > 0 ? (value / total) : 1;
  }

  addResource(getCb) {
    return new Promise((accept, reject) => {
      const resource = new Resource(getCb);
      resource.onupdate = () => {
        if (resource.value >= resource.total) {
          this.resources.splice(this.resources.indexOf(resource), 1);
          
          resource.onupdate = null;
          
          accept();
        }

        const e = new Event('update');
        e.value = this.getValue();
        e.total = this.getTotal();
        e.progress = this.getProgress();
        this.dispatchEvent(e);
      };
      this.resources.push(resource);
      this.queue.push(resource);
      
      this.drain();
    });
  }
  
  drain() {
    if (this.queue.length > 0 && this.numRunning < maxParallelResources) {
      const resource = this.queue.shift();
      resource.get()
        .catch(err => {
          console.warn(err.stack);
        })
        .finally(() => {
          resource.destroy();
          
          this.numRunning--;
          
          this.drain();
        });
      
      this.numRunning++;
    } else {
      const _isDone = () => this.numRunning === 0 && this.queue.length === 0;
      if (_isDone()) {
        process.nextTick(() => { // wait one tick for more resources before emitting drain
          if (_isDone()) {
            this.emit('drain');
          }
        });
      }
    }
  }
}
GlobalContext.Resources = Resources;

const _fromAST = (node, window, parentNode, ownerDocument, uppercase) => {
  if (node.nodeName === '#text') {
    const text = new DOM.Text(node.value);
    text.parentNode = parentNode;
    text.ownerDocument = ownerDocument;
    return text;
  } else if (node.nodeName === '#comment') {
    const comment = new DOM.Comment(node.data);
    comment.parentNode = parentNode;
    comment.ownerDocument = ownerDocument;
    return comment;
  } else {
    let {tagName} = node;
    if (tagName && uppercase) {
      tagName = tagName.toUpperCase();
    }
    let {attrs, value, content, childNodes, sourceCodeLocation} = node;
    const HTMLElementTemplate = window[symbols.htmlTagsSymbol][tagName];
    const location = sourceCodeLocation  ? {
      line: sourceCodeLocation.startLine,
      col: sourceCodeLocation.startCol,
    } : null;
    const element = HTMLElementTemplate ?
      new HTMLElementTemplate(
        attrs,
        value,
        location,
      )
    :
      new DOM.HTMLElement(
        tagName,
        attrs,
        value,
        location,
      );
    element.parentNode = parentNode;
    if (!ownerDocument) { // if there is no owner document, it's us
      ownerDocument = element;
      ownerDocument.defaultView = window;
    }
    element.ownerDocument = ownerDocument;
    if (content) {
      element.childNodes = new DOM.NodeList(
        content.childNodes.map(childNode =>
          _fromAST(childNode, window, element, ownerDocument, uppercase)
        )
      );
    } else if (childNodes) {
      element.childNodes = new DOM.NodeList(
        childNodes.map(childNode =>
          _fromAST(childNode, window, element, ownerDocument, uppercase)
        )
      );
    }
    return element;
  }
};
module.exports._fromAST = _fromAST;
GlobalContext._fromAST = _fromAST;

// To "run" the HTML means to walk it and execute behavior on the elements such as <script src="...">.
// Each candidate element exposes a method on runSymbol which returns whether to await the element load or not.
const _runHtml = (element, window) => {
  if (element instanceof DOM.HTMLElement) {
    return new Promise((accept, reject) => {
      const {document} = window;

      element.traverse(el => {
        const {id} = el;
        if (id) {
          el._emit('attribute', 'id', id);
        }

        if (el[symbols.runSymbol]) {
          document[symbols.addRunSymbol](el[symbols.runSymbol].bind(el));
        }

        if (/\-/.test(el.tagName)) {
          const constructor = window.customElements.get(el.tagName);
          if (constructor) {
            window.customElements.upgrade(el, constructor);
          }
        }
      });
      if (document[symbols.runningSymbol]) {
        document.once('flush', () => {
          accept();
        });
      } else {
        accept();
      }
    });
  } else {
    return Promise.resolve();
  }
};
module.exports._runHtml = _runHtml;
GlobalContext._runHtml = _runHtml;

class DocumentType {}
module.exports.DocumentType = DocumentType;

class DOMImplementation {
  constructor(window) {
    this._window = window;
  }

  createDocument() {
    throw new Error('not implemented');
  }

  createDocumentType() {
    return new DocumentType();
  }

  createHTMLDocument() {
    return _parseDocument('', this._window);
  }

  hasFeature() {
    return false;
  }
}
module.exports.DOMImplementation = DOMImplementation;

class Document extends DOM.HTMLLoadableElement {
  constructor() {
    super('DOCUMENT');

    this.hidden = false;
  }

  get nodeType() {
    return DOM.Node.DOCUMENT_NODE;
  }

  get pointerLockElement() {
    if (this.defaultView.top === this.defaultView) {
      return this[symbols.pointerLockElementSymbol];
    } else {
      return this.defaultView.top.document.pointerLockElement;
    }
  }
  set pointerLockElement(pointerLockElement) {}
  get fullscreenElement() {
    if (this.defaultView.top === this.defaultView) {
      return this[symbols.fullscreenElementSymbol];
    } else {
      return this.defaultView.top.document.fullscreenElement;
    }
  }
  set fullscreenElement(fullscreenElement) {}

  exitPointerLock() {
    const topDocument = this.defaultView.top.document;

    if (topDocument[symbols.pointerLockElementSymbol] !== null) {
      topDocument[symbols.pointerLockElementSymbol] = null;

      process.nextTick(() => {
        topDocument._emit('pointerlockchange');
      });
    }
  }
  exitFullscreen() {
    const topDocument = this.defaultView.top.document;

    if (topDocument[symbols.fullscreenElementSymbol] !== null) {
      topDocument[symbols.fullscreenElementSymbol] = null;

      process.nextTick(() => {
        topDocument._emit('fullscreenchange');
      });
    }
  }
  hasFocus() {
    return (this.defaultView.top === this.defaultView);
  }
}
module.exports.Document = Document;
// FIXME: Temporary until refactor out into modules more and not have circular dependencies.
GlobalContext.Document = Document;

class DocumentFragment extends DOM.HTMLElement {
  constructor() {
    super('DOCUMENTFRAGMENT');
  }

  get nodeType() {
    return DOM.Node.DOCUMENT_FRAGMENT_NODE;
  }
}
module.exports.DocumentFragment = DocumentFragment;
GlobalContext.DocumentFragment = DocumentFragment;

class Range extends DocumentFragment {
  constructor() {
    super('RANGE');
  }

  createContextualFragment(str) {
    var fragment = this.ownerDocument.createDocumentFragment();
    fragment.innerHTML = str;
    return fragment;
  }
}
module.exports.Range = Range;
