const events = require('events');
const {EventEmitter} = events;
const path = require('path');
const fs = require('fs');
const url = require('url');
const http = require('http');
const https = require('https');
const ws = require('ws');
const os = require('os');
const util = require('util');
const {URL} = url;
const {TextEncoder, TextDecoder} = util;
const {XRRigidTransform} = require('./XR.js');
const {performance} = require('perf_hooks');
const {
  workerData: {
    args: {
      options,
      args,
      version,
      xrState,
    },
  },
} = require('worker_threads');

const mkdirp = require('mkdirp');

const {FileReader} = require('./File.js');

const {XMLHttpRequest: XMLHttpRequestBase, FormData} = require('window-xhr');

const fetch = require('window-fetch');
const {Request, Response, Headers, Blob} = fetch;

const WebSocket = require('ws/lib/websocket');
const {
  /* getUserMedia,
  MediaStream,
  MediaStreamTrack,
  RTCDataChannel,
  RTCDataChannelEvent, */
  RTCIceCandidate,
  RTCPeerConnection,
  /* RTCPeerConnectionIceEvent,
  RTCRtpReceiver,
  RTCRtpSender,
  RTCRtpTransceiver, */
  RTCSessionDescription,
} = require('./RTC/index.js');

const {LocalStorage} = require('node-localstorage');
const indexedDB = require('fake-indexeddb');
const parseXml = require('@rgrove/parse-xml');
const THREE = require('../lib/three-min.js');
const {
  MRDisplay,
  VRDisplay,
  FakeVRDisplay,
  VRFrameData,
  VRPose,
  VRStageParameters,
  Gamepad,
  GamepadButton,
  getGamepads,
} = require('./VR.js');

const {defaultCanvasSize} = require('./constants');
const GlobalContext = require('./GlobalContext');
const symbols = require('./symbols');
const {urls} = require('./urls');

const {
  nativeImage: Image,
  nativeImageData: ImageData,
  nativeImageBitmap: ImageBitmap,
  nativePath2D: Path2D,
  nativeCanvasGradient: CanvasGradient,
  nativeCanvasRenderingContext2D: CanvasRenderingContext2D,
  nativeGl: WebGLRenderingContext,
  nativeGl2: WebGL2RenderingContext,
  nativeAudio: {
    AudioContext,
    AudioNode,
    AudioBufferSourceNode,
    OscillatorNode,
    AudioDestinationNode,
    AudioParam,
    AudioListener,
    GainNode,
    AnalyserNode,
    PannerNode,
    StereoPannerNode,
    MicrophoneMediaStream,
  },
  nativeVideo: {
    Video,
    VideoDevice,
  },
  nativeVr,
  nativeMl,
  nativeBrowser,
  nativeWindow,
} = require('./native-bindings');

const nativeWorker = require('worker-native');

const eventLoopNative = require('event-loop-native');
nativeWindow.setEventLoop(eventLoopNative);
nativeWorker.dlclose(eventLoopNative.getDlibPath());

GlobalContext.args = args;
GlobalContext.version = version;
GlobalContext.xrState = xrState;

const {_parseDocument, _parseDocumentAst, Document, DocumentFragment, DocumentType, DOMImplementation, initDocument} = require('./Document');
const {
  Element,
  HTMLElement,
  HTMLBodyElement,
  HTMLAnchorElement,
  HTMLStyleElement,
  HTMLScriptElement,
  HTMLLinkElement,
  HTMLImageElement,
  HTMLAudioElement,
  HTMLVideoElement,
  HTMLSourceElement,
  HTMLIFrameElement,
  SVGElement,
  HTMLCanvasElement,
  HTMLTemplateElement,
  createImageBitmap,
  DOMRect,
  DOMPoint,
  Node,
  NodeList,
  Text,
  Comment,
  HTMLCollection,
} = require('./DOM');
const {CustomEvent, DragEvent, ErrorEvent, Event, EventTarget, KeyboardEvent, MessageEvent, MouseEvent, WheelEvent, PromiseRejectionEvent} = require('./Event');
const {History} = require('./History');
const {Location} = require('./Location');
const {XMLHttpRequest} = require('./Network');
const XR = require('./XR');
const DevTools = require('./DevTools');
const utils = require('./utils');
const {_elementGetter, _elementSetter, _download} = utils;

const btoa = s => Buffer.from(s, 'binary').toString('base64');
const atob = s => Buffer.from(s, 'base64').toString('binary');

const isMac = os.platform() === 'darwin';

const zeroMatrix = new THREE.Matrix4();
const localFloat32Array = zeroMatrix.toArray(new Float32Array(16));
const localFloat32Array2 = zeroMatrix.toArray(new Float32Array(16));
const localFloat32Array3 = zeroMatrix.toArray(new Float32Array(16));
const localFloat32Array4 = new Float32Array(16);
const localFovArray = new Float32Array(4);
const localGamepadArray = new Float32Array(24);

// const handEntrySize = (1 + (5 * 5)) * (3 + 3);
const transformArray = new Float32Array(7 * 2);
const projectionArray = new Float32Array(16 * 2);
/* const handsArray = [
  new Float32Array(handEntrySize),
  new Float32Array(handEntrySize),
]; */
const controllersArray = new Float32Array((1 + 3 + 4 + 6) * 2);

const localVector = new THREE.Vector3();
const localVector2 = new THREE.Vector3();
const localQuaternion = new THREE.Quaternion();
const localMatrix = new THREE.Matrix4();
const localMatrix2 = new THREE.Matrix4();
const _normalizeMatrixArray = float32Array => {
  if (isNaN(float32Array[0])) {
    zeroMatrix.toArray(float32Array);
  }
};

const windows = [];
const contexts = [];
GlobalContext.contexts = contexts;

const vrPresentState = {
  vrContext: null,
  system: null,
  compositor: null,
  glContextId: 0,
  msFbo: null,
  msTex: null,
  msDepthTex: null,
  fbo: null,
  tex: null,
  depthTex: null,
  hasPose: false,
  // lmContext: null,
  layers: [],
};
GlobalContext.vrPresentState = vrPresentState;
const _getVrGlContext = () => contexts.find(context => context.id === vrPresentState.glContextId);

const mlPresentState = {
  mlContext: null,
  mlFbo: null,
  mlTex: null,
  mlDepthTex: null,
  mlMsFbo: null,
  mlMsTex: null,
  mlMsDepthTex: null,
  mlGlContextId: 0,
  mlCleanups: null,
  mlHasPose: false,
  layers: [],
};
GlobalContext.mlPresentState = mlPresentState;
const _getMlGlContext = () => contexts.find(context => context.id === mlPresentState.mlGlContextId);

const fakePresentState = {
  fakeVrDisplay: null,
  layers: [],
};
GlobalContext.fakePresentState = fakePresentState;
GlobalContext.fakeVrDisplayEnabled = false;

class CustomElementRegistry {
  constructor(window) {
    this._window = window;

    this.elements = {};
    this.elementPromises = {};
  }

  define(name, constructor, options) {
    name = name.toUpperCase();

    this.elements[name] = constructor;

    this._window.document.traverse(el => {
      if (el.tagName === name) {
        this.upgrade(el, constructor);
      }
    });

    const promises = this.elementPromises[name];
    if (promises) {
      for (let i = 0; i < promises.length; i++) {
        promises[i].accept();
      }
      this.elementPromises[name] = null;
    }
  }
  get(name) {
    name = name.toUpperCase();

    return this.elements[name];
  }
  whenDefined(name) {
    name = name.toUpperCase();

    if (this.elements[name]) {
      return Promise.resolve();
    } else {
      let promises = this.elementPromises[name];
      if (!promises) {
        promises = [];
        this.elementPromises[name] = promises;
      }
      const promise = new Promise((accept, reject) => {
        promise.accept = accept;
        promise.reject = reject;
      });
      promises.push(promise);
      return promise;
    }
  }

  upgrade(el, constructor) {
    Object.setPrototypeOf(el, constructor.prototype);
    constructor.call(el);
  }
}

class MonitorManager {
  getList() {
    return nativeWindow.getMonitors();
  }

  select(index) {
    nativeWindow.setMonitor(index);
  }
}

class Screen {
  constructor(window) {
    this._window = window;
  }

  get top() {
    return 0;
  }
  set top(top) {}
  get left() {
    return 0;
  }
  set left(left) {}
  get width() {
    return this._window.innerWidth;
  }
  set width(width) {}
  get height() {
    return this._window.innerHeight;
  }
  set height(height) {}
  get colorDepth() {
    return 24;
  }
  set colorDepth(colorDepth) {}
  get orientation() {
    return {
      angle: 0,
      type: 'landscape-primary',
      onchange: null,
    };
  }
  set orientation(orientation) {}

  get pixelDepth() {
    return this.colorDepth;
  }
  set pixelDepth(pixelDepth) {}
  get availTop() {
    return this.top;
  }
  set availTop(availTop) {}
  get availLeft() {
    return this.left;
  }
  set availLeft(availLeft) {}
  get availWidth() {
    return this.width;
  }
  set availWidth(availWidth) {}
  get availHeight() {
    return this.height;
  }
  set availHeight(availHeight) {}
}

class MediaRecorder extends EventEmitter {
  constructor() {
    super();
  }

  start() {}

  stop() {}

  requestData() {}
}

class DataTransfer {
  constructor({items = [], files = []} = {}) {
    this.items = items;
    this.files = files;
  }
}
class DataTransferItem {
  constructor(kind = 'string', type = 'text/plain', data = null) {
    this.kind = kind;
    this.type = type;
    this.data = data;
  }

  getAsFile() {
    return new Blob([this.data], {
      type: this.type,
    });
  }

  getAsString(callback) {
    const {data} = this;
    setImmediate(() => {
      callback(data);
    });
  }
}

class Worker {
  constructor(src) {
    this.worker = nativeWorker.make({
      initModule: path.join(__dirname, 'Worker.js'),
      args: {
        src,
      },
    });
  }

  postMessage(message, transferList) {
    this.worker.postMessage(message, transferList);
  }

  get onmessage() {
    return this.worker.onmessage;
  }
  set onmessage(onmessage) {
    this.worker.onmessage = onmessage;
  }
  get onerror() {
    return this.worker.onerror;
  }
  set onerror(onerror) {
    this.worker.onerror = onerror;
  }
}

let rafIndex = 0;
const _findFreeSlot = a => {
  let i;
  for (i = 0; i < a.length; i++) {
    if (a[i] === null) {
      break;
    }
  }
  return i;
};
const _makeRequestAnimationFrame = window => (fn, priority = 0) => {
  fn = fn.bind(window);
  fn[symbols.prioritySymbol] = priority;
  const id = ++rafIndex;
  fn[symbols.idSymbol] = id;
  const rafCbs = window[symbols.rafCbsSymbol];
  rafCbs[_findFreeSlot(rafCbs)] = fn;
  rafCbs.sort((a, b) => (b ? b[symbols.prioritySymbol] : 0) - (a ? a[symbols.prioritySymbol] : 0));
  return id;
};
const _makeOnRequestHitTest = window => (origin, direction, cb) => nativeMl.RequestHitTest(origin, direction, cb, window);

const _normalizeUrl = utils._makeNormalizeUrl(options.baseUrl);

(window => {
  const HTMLImageElementBound = (Old => class HTMLImageElement extends Old {
    constructor() {
      super(...arguments);

      // need to set owner document here because HTMLImageElement can be manually constructed via new Image()
      this.ownerDocument = window.document;
    }
  })(HTMLImageElement);

  const HTMLAudioElementBound = (Old => class HTMLAudioElement extends Old {
    constructor(src) {
      if (typeof src === 'string') {
        const audio = new HTMLAudioElementBound();
        audio.setAttribute('src', src);
        return audio;
      } else {
        super(...arguments);

        // need to set owner document here because HTMLAudioElement can be manually constructed via new Audio()
        this.ownerDocument = window.document;
      }
    }
  })(HTMLAudioElement);

  for (const k in EventEmitter.prototype) {
    window[k] = EventEmitter.prototype[k];
  }
  EventEmitter.call(window);

  window.window = window;
  window.self = window;
  window.parent = options.parent || window;
  window.top = options.top || window;

  window.innerWidth = defaultCanvasSize[0];
  window.innerHeight = defaultCanvasSize[1];
  window.devicePixelRatio = 1;
  const location = new Location(options.url);
  Object.defineProperty(window, 'location', {
    get() {
      return location;
    },
    set(href) {
      href = href + '';
      location.href = href;
    },
  });
  window.history = new History(location.href);
  window.navigator = {
    userAgent: `MixedReality (Exokit ${GlobalContext.version})`,
    vendor: 'MixedReality',
    platform: os.platform(),
    hardwareConcurrency: os.cpus().length,
    appCodeName: 'Mozilla',
    appName: 'Netscape',
    appVersion: '5.0',
    mediaDevices: {
      getUserMedia(constraints) {
        if (constraints.audio) {
          return Promise.resolve(new MicrophoneMediaStream());
        } else if (constraints.video) {
          const dev = new VideoDevice();
          dev.constraints = constraints.video;
          return Promise.resolve(dev);
        } else {
          return Promise.reject(new Error('constraints not met'));
        }
      },
    },
    getVRDisplaysSync() {
      const result = [];
      if (GlobalContext.fakeVrDisplayEnabled) {
        result.push(window[symbols.mrDisplaysSymbol].fakeVrDisplay);
      }
      if (nativeMl && nativeMl.IsPresent()) {
        result.push(window[symbols.mrDisplaysSymbol].mlDisplay);
      }
      if (nativeVr && nativeVr.VR_IsHmdPresent()) {
        result.push(window[symbols.mrDisplaysSymbol].vrDisplay);
      }
      result.sort((a, b) => +b.isPresenting - +a.isPresenting);
      return result;
    },
    createVRDisplay() {
      GlobalContext.fakeVrDisplayEnabled = true;
      return window[symbols.mrDisplaysSymbol].fakeVrDisplay;
    },
    getGamepads,
    clipboard:{
      read:() => Promise.resolve(), // Not implemented yet
      readText: () => new Promise(resolve => {
        resolve(nativeWindow.getClipboard().slice(0, 256));// why do we slice this?
      }),
      write:() => Promise.resolve(), // Not implemented yet
      writeText: clipboardContents => new Promise(resolve => {
        nativeWindow.setClipboard(clipboardContents);
        resolve();
      })
    }
  };

  // WebVR enabled.
  if (['all', 'webvr'].includes(options.args.xr)) {
    window.navigator.getVRDisplays = function() {
      return Promise.resolve(this.getVRDisplaysSync());
    }
  }

  // WebXR enabled.
  if (['all', 'webxr'].includes(options.args.xr)) {
    window.navigator.xr = new XR.XR(window);
  }

  window.destroy = function() {
    this._emit('destroy', {window: this});
  };
  window.URL = URL;
  window.console = console;
  window.setTimeout = (setTimeout => (fn, timeout, args) => {
    fn = fn.bind.apply(fn, [window].concat(args));
    let id = _findFreeSlot(timeouts);
    id++;
    timeouts[id] = fn;
    fn[symbols.timeoutSymbol] = setTimeout(fn, timeout, args);
    return id;
  })(setTimeout);
  window.clearTimeout = (clearTimeout => id => {
    id--;
    const fn = timeouts[id];
    if (fn) {
      clearTimeout(fn[symbols.timeoutSymbol]);
      timeouts[id] = null;
    }
  })(clearTimeout);
  window.setInterval = (setInterval => (fn, interval, args) => {
    if (interval < 10) {
      interval = 10;
    }
    fn = fn.bind.apply(fn, [window].concat(args));
    let id = _findFreeSlot(intervals);
    id++;
    intervals[id] = fn;
    fn[symbols.timeoutSymbol] = setInterval(fn, interval, args);
    return id;
  })(setInterval);
  window.clearInterval = (clearInterval => id => {
    id--;
    const fn = intervals[id];
    if (fn) {
      clearInterval(fn[symbols.timeoutSymbol]);
      intervals[id] = null;
    }
  })(clearInterval);
  const _maybeDownload = (m, u, data, bufferifyFn) => options.args.download ? _download(m, u, data, bufferifyFn, options.args.download) : data;
  window.fetch = (u, options) => {
    const _boundFetch = (u, options) => fetch(u, options)
      .then(res => {
        const method = (options && options.method) || 'GET';
        res.arrayBuffer = (fn => function() {
          return fn.apply(this, arguments)
            .then(ab => _maybeDownload(method, u, ab, ab => Buffer.from(ab)));
        })(res.arrayBuffer);
        res.blob = (fn => function() {
          return fn.apply(this, arguments)
            .then(blob => _maybeDownload(method, u, blob, blob => blob.buffer));
        })(res.blob);
        res.json = (fn => function() {
          return fn.apply(this, arguments)
            .then(j => _maybeDownload(method, u, j, j => Buffer.from(JSON.stringify(j))));
        })(res.json);
        res.text = (fn => function() {
          return fn.apply(this, arguments)
            .then(t => _maybeDownload(method, u, t, t => Buffer.from(t, 'utf8')));
        })(res.text);

        return res;
      });

    if (typeof u === 'string') {
      const blob = urls.get(u);
      if (blob) {
        return Promise.resolve(new Response(blob));
      } else {
        u = _normalizeUrl(u);
        return _boundFetch(u, options);
      }
    } else {
      return _boundFetch(u, options);
    }
  };
  window.Request = Request;
  window.Response = Response;
  window.Headers = Headers;
  window.Blob = Blob;
  window.FormData = FormData;
  window.XMLHttpRequest = (Old => {
    class XMLHttpRequest extends Old {
      open(method, url, async, username, password) {
        url = _normalizeUrl(url);
        return super.open(method, url, async, username, password);
      }
      get response() {
        return _maybeDownload(this._properties.method, this._properties.uri, super.response, o => {
          switch (this.responseType) {
            case 'arraybuffer': return Buffer.from(o);
            case 'blob': return o.buffer;
            case 'json': return Buffer.from(JSON.stringify(o), 'utf8');
            case 'text': return Buffer.from(o, 'utf8');
            default: throw new Error(`cannot download responseType ${responseType}`);
          }
        });
      }
    }
    for (const k in XMLHttpRequestBase) {
      XMLHttpRequest[k] = XMLHttpRequestBase[k];
    }
    return XMLHttpRequest;
  })(XMLHttpRequest);
  window.WebSocket = WebSocket;
  window.event = new Event(); // XXX this needs to track the current event
  window.localStorage = new LocalStorage(path.join(options.dataPath, '.localStorage'));
  window.sessionStorage = new LocalStorage(path.join(options.dataPath, '.sessionStorage'));
  window.indexedDB = indexedDB;
  window.performance = performance;
  window.screen = new Screen(window);
  window.urls = urls; // XXX non-standard
  window.scrollTo = function(x = 0, y = 0) {
    this.scrollX = x;
    this.scrollY = y;
  };
  window.scrollX = 0;
  window.scrollY = 0;
  window[symbols.htmlTagsSymbol] = {
    DOCUMENT: Document,
    BODY: HTMLBodyElement,
    A: HTMLAnchorElement,
    STYLE: HTMLStyleElement,
    SCRIPT: HTMLScriptElement,
    LINK: HTMLLinkElement,
    IMG: HTMLImageElementBound,
    AUDIO: HTMLAudioElementBound,
    VIDEO: HTMLVideoElement,
    SOURCE: HTMLSourceElement,
    IFRAME: HTMLIFrameElement,
    CANVAS: HTMLCanvasElement,
    TEMPLATE: HTMLTemplateElement,
  };
  window[symbols.optionsSymbol] = options;
  window[symbols.styleEpochSymbol] = 0;
  window.DocumentFragment = DocumentFragment;

  // DOM.
  window.Element = Element;
  window.HTMLElement = HTMLElement;
  window.HTMLAnchorElement = HTMLAnchorElement;
  window.HTMLStyleElement = HTMLStyleElement;
  window.HTMLLinkElement = HTMLLinkElement;
  window.HTMLScriptElement = HTMLScriptElement;
  window.HTMLImageElement = HTMLImageElementBound,
  window.HTMLAudioElement = HTMLAudioElementBound;
  window.HTMLVideoElement = HTMLVideoElement;
  window.SVGElement = SVGElement;
  window.HTMLIFrameElement = HTMLIFrameElement;
  window.HTMLCanvasElement = HTMLCanvasElement;
  window.HTMLTemplateElement = HTMLTemplateElement;
  window.Node = Node;
  window.Text = Text;
  window.Comment = Comment;
  window.NodeList = NodeList;
  window.HTMLCollection = HTMLCollection;

  /* window.MediaStream = MediaStream;
  window.MediaStreamTrack = MediaStreamTrack;
  window.RTCDataChannel = RTCDataChannel;
  window.RTCDataChannelEvent = RTCDataChannelEvent;
  window.RTCIceCandidate = RTCIceCandidate;
  window.RTCPeerConnection = RTCPeerConnection;
  window.RTCPeerConnectionIceEvent = RTCPeerConnectionIceEvent;
  window.RTCRtpReceiver = RTCRtpReceiver;
  window.RTCRtpSender = RTCRtpSender;
  window.RTCRtpTransceiver = RTCRtpTransceiver;
  window.RTCSessionDescription = RTCSessionDescription; */
  window.MediaStream = class MediaStream {};
  window.RTCPeerConnection = RTCPeerConnection;
  window.RTCSessionDescription = RTCSessionDescription;
  window.RTCIceCandidate = RTCIceCandidate;

  window.customElements = new CustomElementRegistry(window);
  window.CustomElementRegistry = CustomElementRegistry;
  window.MutationObserver = require('./MutationObserver').MutationObserver;
  window.DOMRect = DOMRect;
  window.DOMPoint = DOMPoint;
  window.getComputedStyle = el => {
    let styleSpec = el[symbols.computedStyleSymbol];
    if (!styleSpec || styleSpec.epoch !== window[symbols.styleEpochSymbol]) {
      const style = el.style.clone();
      const stylesheetEls = el.ownerDocument.documentElement.getElementsByTagName('style')
        .concat(el.ownerDocument.documentElement.getElementsByTagName('link'));
      for (let i = 0; i < stylesheetEls.length; i++) {
        const {stylesheet} = stylesheetEls[i];
        if (stylesheet) {
          const {rules} = stylesheet;
          for (let j = 0; j < rules.length; j++) {
            const rule = rules[j];
            const {selectors} = rule;
            if (selectors && selectors.some(selector => el.matches(selector))) {
              const {declarations} = rule;
              for (let k = 0; k < declarations.length; k++) {
                const {property, value} = declarations[k];
                style[property] = value;
              }
            }
          }
        }
      }
      styleSpec = {
        style,
        styleEpoch: window[symbols.styleEpochSymbol],
      };
      el[symbols.computedStyleSymbol] = styleSpec;
    }
    return styleSpec.style;
  };
  window.browser = {
    devTools: DevTools,
    http,
    // https,
    ws,
    createRenderTarget: nativeWindow.createRenderTarget, // XXX needed for reality tabs fakeDisplay
    magicleap: nativeMl ? {
      RequestMeshing: () => nativeMl.RequestMeshing(window),
      RequestPlaneTracking: () => nativeMl.RequestPlaneTracking(window),
      RequestHandTracking: () => nativeMl.RequestHandTracking(window),
      RequestEyeTracking: () => nativeMl.RequestEyeTracking(window),
      RequestImageTracking: (img, size) => nativeMl.RequestImageTracking(window, img, size),
      RequestDepthPopulation: nativeMl.RequestDepthPopulation,
      RequestCamera: nativeMl.RequestCamera,
    } : null,
    monitors: new MonitorManager(),
  };
  window.DOMParser = class DOMParser {
    parseFromString(htmlString, type) {
      const _recurse = node => {
        let nodeName = null;
        let value = null;
        if (node.type === 'text') {
          nodeName = '#text';
          value = node.text;
        } else if (node.type === 'comment') {
          nodeName = '#comment';
          value = node.content;
        }

        const tagName = node.name || null;

        const attrs = [];
        if (node.attributes) {
          for (const name in node.attributes) {
            attrs.push({
              name,
              value: node.attributes[name],
            });
          }
        }

        const childNodes = node.children ? node.children.map(childNode => _recurse(childNode)) : [];

        return {
          nodeName,
          tagName,
          attrs,
          value,
          childNodes,
        };
      };
      const xmlAst = parseXml(htmlString, {
        // preserveComments: true,
      });
      const htmlAst = _recurse(xmlAst);
      return _parseDocumentAst(htmlAst, window, false);
    }
  };
  // window.Buffer = Buffer; // XXX non-standard
  window.Event = Event;
  window.KeyboardEvent = KeyboardEvent;
  window.MouseEvent = MouseEvent;
  window.WheelEvent = WheelEvent;
  window.DragEvent = DragEvent;
  window.MessageEvent = MessageEvent;
  window.PromiseRejectionEvent = PromiseRejectionEvent;
  window.CustomEvent = CustomEvent;
  window.addEventListener = EventTarget.prototype.addEventListener.bind(window);
  window.removeEventListener = EventTarget.prototype.removeEventListener.bind(window);
  window.dispatchEvent = EventTarget.prototype.dispatchEvent.bind(window);
  window.Image = HTMLImageElementBound;
  window.ImageData = ImageData;
  window.ImageBitmap = ImageBitmap;
  window.Path2D = Path2D;
  window.CanvasGradient = CanvasGradient;
  window.CanvasRenderingContext2D = CanvasRenderingContext2D;
  window.WebGLRenderingContext = WebGLRenderingContext;
  if (options.args.webgl !== '1') {
    window.WebGL2RenderingContext = WebGL2RenderingContext;
  }
  window.Audio = HTMLAudioElementBound;
  window.MediaRecorder = MediaRecorder;
  window.Document = Document;
  window.DocumentType = DocumentType;
  window.DOMImplementation = DOMImplementation;
  window.DataTransfer = DataTransfer;
  window.DataTransferItem = DataTransferItem;
  window.FileReader = FileReader;
  window.Screen = Screen;
  window.Gamepad = Gamepad;
  window.VRStageParameters = VRStageParameters;
  window.VRDisplay = VRDisplay;
  window.FakeVRDisplay = FakeVRDisplay;
  // window.ARDisplay = ARDisplay;
  window.VRFrameData = VRFrameData;
  if (window.navigator.xr) {
    window.XR = XR.XR;
    window.XRDevice = XR.XRDevice;
    window.XRSession = XR.XRSession;
    window.XRWebGLLayer = XR.XRWebGLLayer;
    window.XRPresentationFrame = XR.XRPresentationFrame;
    window.XRView = XR.XRView;
    window.XRViewport = XR.XRViewport;
    window.XRDevicePose = XR.XRDevicePose;
    window.XRInputSource = XR.XRInputSource;
    window.XRRay = XR.XRRay;
    window.XRInputPose = XR.XRInputPose;
    window.XRInputSourceEvent = XR.XRInputSourceEvent;
    window.XRCoordinateSystem = XR.XRCoordinateSystem;
    window.XRFrameOfReference = XR.XRFrameOfReference;
    window.XRStageBounds = XR.XRStageBounds;
    window.XRStageBoundsPoint = XR.XRStageBoundsPoint;
  }
  window.btoa = btoa;
  window.atob = atob;
  window.TextEncoder = TextEncoder;
  window.TextDecoder = TextDecoder;
  window.AudioContext = AudioContext;
  window.AudioNode = AudioNode;
  window.AudioBufferSourceNode = AudioBufferSourceNode;
  window.OscillatorNode = OscillatorNode;
  window.AudioDestinationNode = AudioDestinationNode;
  window.AudioParam = AudioParam;
  window.AudioListener = AudioListener;
  window.GainNode = GainNode;
  window.AnalyserNode = AnalyserNode;
  window.PannerNode = PannerNode;
  window.StereoPannerNode = StereoPannerNode;
  window.createImageBitmap = createImageBitmap;
  window.Worker = class extends Worker {
    constructor(src) {
      if (src instanceof Blob) {
        super('data:application/javascript,' + src.buffer.toString('utf8'));
      } else {
        const blob = urls.get(src);
        const normalizedSrc = blob ?
          'data:application/octet-stream;base64,' + blob.buffer.toString('base64')
        :
          _normalizeUrl(src);
        super(normalizedSrc);
      }
    }
  };
  window.requestAnimationFrame = _makeRequestAnimationFrame(window);
  window.cancelAnimationFrame = id => {
    const index = rafCbs.findIndex(r => r[symbols.idSymbol] === id);
    if (index !== -1) {
      rafCbs[index] = null;
    }
  };
  window.postMessage = (postMessage => function(data) {
    if (window.top === window) {
      setImmediate(() => {
        window._emit('message', new MessageEvent('message', {data}));
      });
    } else {
      postMessage.apply(this, arguments);
    }
  })(window.postMessage);
  /*
    Treat function onload() as a special case that disables automatic event attach for onload, because this is how browsers work. E.g.
      <!doctype html><html><head><script>
        function onload() {
          console.log ('onload'); // NOT called; presence of top-level function onload() makes all the difference
        }
        window.onload = onload;
      </script></head></html>
  */
  window[symbols.disabledEventsSymbol] = {
    load: undefined,
    error: undefined,
  };
  window._emit = function(type) {
    if (!this[symbols.disabledEventsSymbol][type]) {
      Node.prototype._emit.apply(this, arguments);
    }
  };
 /* Object.defineProperty(window, 'onload', {
    get() {
      return window[symbols.disabledEventsSymbol]['load'] !== undefined ? window[symbols.disabledEventsSymbol]['load'] : _elementGetter(window, 'load');
    },
    set(onload) {
      if (nativeVm.isCompiling()) {
        this[symbols.disabledEventsSymbol]['load'] = onload;
      } else {
        if (window[symbols.disabledEventsSymbol]['load'] !== undefined) {
          this[symbols.disabledEventsSymbol]['load'] = onload;
        } else {
          _elementSetter(window, 'load', onload);
        }
      }
    },
  });
  Object.defineProperty(window, 'onerror', {
    get() {
      return window[symbols.disabledEventsSymbol]['error'] !== undefined ? window[symbols.disabledEventsSymbol]['error'] : _elementGetter(window, 'error');
    },
    set(onerror) {
      if (nativeVm.isCompiling()) {
        window[symbols.disabledEventsSymbol]['error'] = onerror;
      } else {
        if (window[symbols.disabledEventsSymbol]['error'] !== undefined) {
          window[symbols.disabledEventsSymbol]['error'] = onerror;
        } else {
          _elementSetter(window, 'error', onerror);
        }
      }
    },
  }); */
  Object.defineProperty(window, 'onload', {
    get() {
      return _elementGetter(window, 'load');
    },
    set(onload) {
      _elementSetter(window, 'load', onload);
    },
  });
  Object.defineProperty(window, 'onerror', {
    get() {
      return _elementGetter(window, 'error');
    },
    set(onerror) {
      _elementSetter(window, 'error', onerror);
    },
  });
  Object.defineProperty(window, 'onpopstate', {
    get() {
      return _elementGetter(window, 'popstate');
    },
    set(onpopstate) {
      _elementSetter(window, 'popstate', onpopstate);
    },
  });

  window.history.on('popstate', (u, state) => {
    window.location.set(u);

    const event = new Event('popstate');
    event.state = state;
    window.dispatchEvent(event);
  });
  let loading = false;
  window.location.on('update', href => {
    if (!loading) {
      exokit.load(href, {
        dataPath: options.dataPath,
      })
        .then(newWindow => {
          window._emit('beforeunload');
          window._emit('unload');
          window._emit('navigate', newWindow);
        })
        .catch(err => {
          loading = false;

          const e = new ErrorEvent('error', {target: this});
          e.message = err.message;
          e.stack = err.stack;
          this.dispatchEvent(e);
        });
      loading = true;
    }
  });
  
  const rafCbs = [];
  window[symbols.rafCbsSymbol] = rafCbs;
  const timeouts = [];
  const intervals = [];
  const localCbs = [];
  const _cacheLocalCbs = cbs => {
    for (let i = 0; i < cbs.length; i++) {
      localCbs[i] = cbs[i];
    }
    for (let i = cbs.length; i < localCbs.length; i++) {
      localCbs[i] = null;
    }
  };
  const _clearLocalCbs = () => {
    for (let i = 0; i < localCbs.length; i++) {
      localCbs[i] = null;
    }
  };
  const _tickAnimationFrameRaf = top => async () => {
    const childSyncs = (await Promise.all(windows.map(window => window.tickAnimationFrame(GlobalContext.contexts.length > 0 ? 'child' : 'top')))).flat();
    for (let i = 0; i < GlobalContext.contexts.length; i++) {
      GlobalContext.contexts[i].setPrereqSyncs(childSyncs);
    }

    if (rafCbs.length > 0) {
      _cacheLocalCbs(rafCbs);
      
      const performanceNow = performance.now();

      for (let i = 0; i < localCbs.length; i++) {
        const rafCb = localCbs[i];
        if (rafCb) {
          try {
            rafCb(performanceNow);
          } catch (e) {
            console.warn(e);
          }

          const index = rafCbs.indexOf(rafCb); // could have changed due to sorting
          if (index !== -1) {
            rafCbs[index] = null;
          }
        }
      }

      _clearLocalCbs(); // release garbage
    }

    const syncs = [];
    for (let i = 0; i < GlobalContext.contexts.length; i++) {
      const context = GlobalContext.contexts[i];
      
      if (context.isDirty && context.isDirty()) {
        if (!top) {
          nativeWindow.setCurrentWindowContext(context.getWindowHandle());
          syncs.push(nativeWindow.getSync());
        }
        
        context.clearDirty();
      }

      context.clearPrereqSyncs();
    }
    for (let i = 0; i < childSyncs.length; i++) {
      nativeWindow.deleteSync(childSyncs[i]);
    }
    return syncs;
  };
  const _tickAnimationFrameTop = _tickAnimationFrameRaf(true);
  const _tickAnimationFrameChild = _tickAnimationFrameRaf(false);
  const _tickAnimationFrameWait = async () => {
    // perform the wait
    if (fakePresentState.fakeVrDisplay) {
      fakePresentState.fakeVrDisplay.waitGetPoses();
    }
    let vrGlContext, mlGlContext;
    if (vrGlContext = _getVrGlContext()) {
      // wait for frame
      await new Promise((accept, reject) => {
        vrPresentState.compositor.RequestGetPoses(
          vrPresentState.system,
          localFloat32Array, // hmd
          localFloat32Array2, // left controller
          localFloat32Array3, // right controller
          accept
        );
      });

      vrPresentState.hasPose = true;

      _normalizeMatrixArray(localFloat32Array);
      _normalizeMatrixArray(localFloat32Array2);
      _normalizeMatrixArray(localFloat32Array3);

      // build xr state
      const hmdMatrix = localMatrix.fromArray(localFloat32Array);

      hmdMatrix.decompose(localVector, localQuaternion, localVector2);
      localVector.toArray(xrState.position);
      localQuaternion.toArray(xrState.orientation);

      hmdMatrix.getInverse(hmdMatrix);

      vrPresentState.system.GetEyeToHeadTransform(0, localFloat32Array4);
      localMatrix2.fromArray(localFloat32Array4);
      localMatrix2.decompose(localVector, localQuaternion, localVector2);
      localVector.toArray(xrState.leftOffset);
      localMatrix2
        .getInverse(localMatrix2)
        .multiply(hmdMatrix);
      localMatrix2.toArray(xrState.leftViewMatrix);

      vrPresentState.system.GetProjectionMatrix(0, xrState.depthNear[0], xrState.depthFar[0], localFloat32Array4);
      _normalizeMatrixArray(localFloat32Array4);
      xrState.leftProjectionMatrix.set(localFloat32Array4);

      vrPresentState.system.GetProjectionRaw(0, localFovArray);
      for (let i = 0; i < localFovArray.length; i++) {
        xrState.leftFov[i] = Math.atan(localFovArray[i]) / Math.PI * 180;
      }

      vrPresentState.system.GetEyeToHeadTransform(1, localFloat32Array4);
      _normalizeMatrixArray(localFloat32Array4);
      localMatrix2.fromArray(localFloat32Array4);
      localMatrix2.decompose(localVector, localQuaternion, localVector2);
      localVector.toArray(xrState.rightOffset);
      localMatrix2
        .getInverse(localMatrix2)
        .multiply(hmdMatrix);
      localMatrix2.toArray(xrState.rightViewMatrix);

      vrPresentState.system.GetProjectionMatrix(1, xrState.depthNear[0], xrState.depthFar[0], localFloat32Array4);
      _normalizeMatrixArray(localFloat32Array4);
      xrState.rightProjectionMatrix.set(localFloat32Array4);

      vrPresentState.system.GetProjectionRaw(1, localFovArray);
      for (let i = 0; i < localFovArray.length; i++) {
        xrState.rightFov[i] = Math.atan(localFovArray[i]) / Math.PI * 180;
      }

      // build stage parameters
      // vrPresentState.system.GetSeatedZeroPoseToStandingAbsoluteTrackingPose(localFloat32Array4);
      // _normalizeMatrixArray(localFloat32Array4);
      // stageParameters.sittingToStandingTransform.set(localFloat32Array4);

      // build gamepads data
      {
        const leftGamepad = xrState.gamepads[0];
        vrPresentState.system.GetControllerState(0, localGamepadArray);
        if (!isNaN(localGamepadArray[0])) {
          leftGamepad.connected[0] = true;

          localMatrix.fromArray(localFloat32Array2);
          localMatrix.decompose(localVector, localQuaternion, localVector2);
          localVector.toArray(leftGamepad.position);
          localQuaternion.toArray(leftGamepad.orientation);

          leftGamepad.buttons[0].pressed[0] = localGamepadArray[4]; // pad
          leftGamepad.buttons[1].pressed[0] = localGamepadArray[5]; // trigger
          leftGamepad.buttons[2].pressed[0] = localGamepadArray[3]; // grip
          leftGamepad.buttons[3].pressed[0] = localGamepadArray[2]; // menu
          leftGamepad.buttons[4].pressed[0] = localGamepadArray[1]; // system

          leftGamepad.buttons[0].touched[0] = localGamepadArray[9]; // pad
          leftGamepad.buttons[1].touched[0] = localGamepadArray[10]; // trigger
          leftGamepad.buttons[2].touched[0] = localGamepadArray[8]; // grip
          leftGamepad.buttons[3].touched[0] = localGamepadArray[7]; // menu
          leftGamepad.buttons[4].touched[0] = localGamepadArray[6]; // system

          for (let i = 0; i < 10; i++) {
            leftGamepad.axes[i] = localGamepadArray[11+i];
          }
          leftGamepad.buttons[1].value[0] = leftGamepad.axes[2]; // trigger
        } else {
          leftGamepad.connected[0] = 0;
        }
      }

      {
        const rightGamepad = xrState.gamepads[1];
        vrPresentState.system.GetControllerState(1, localGamepadArray);
        if (!isNaN(localGamepadArray[0])) {
          rightGamepad.connected[0] = 1;
          
          localMatrix.fromArray(localFloat32Array3);
          localMatrix.decompose(localVector, localQuaternion, localVector2);
          localVector.toArray(rightGamepad.position);
          localQuaternion.toArray(rightGamepad.orientation);

          rightGamepad.buttons[0].pressed[0] = localGamepadArray[4]; // pad
          rightGamepad.buttons[1].pressed[0] = localGamepadArray[5]; // trigger
          rightGamepad.buttons[2].pressed[0] = localGamepadArray[3]; // grip
          rightGamepad.buttons[3].pressed[0] = localGamepadArray[2]; // menu
          rightGamepad.buttons[4].pressed[0] = localGamepadArray[1]; // system

          rightGamepad.buttons[0].touched[0] = localGamepadArray[9]; // pad
          rightGamepad.buttons[1].touched[0] = localGamepadArray[10]; // trigger
          rightGamepad.buttons[2].touched[0] = localGamepadArray[8]; // grip
          rightGamepad.buttons[3].touched[0] = localGamepadArray[7]; // menu
          rightGamepad.buttons[4].touched[0] = localGamepadArray[6]; // system

          for (let i = 0; i < 10; i++) {
            rightGamepad.axes[i] = localGamepadArray[11+i];
          }
          rightGamepad.buttons[1].value[0] = rightGamepad.axes[2]; // trigger
        } else {
          rightGamepad.connected[0] = 0;
        }
      }

      /* if (vrPresentState.lmContext) { // XXX remove this binding
        vrPresentState.lmContext.WaitGetPoses(handsArray);
      } */
    } else if (mlGlContext = _getMlGlContext()) {
      mlPresentState.mlHasPose = await new Promise((accept, reject) => {
        mlPresentState.mlContext.RequestGetPoses(
          transformArray,
          projectionArray,
          controllersArray,
          accept
        );
      });

      if (mlPresentState.mlHasPose) {
        localVector.fromArray(transformArray, 0);
        localQuaternion.fromArray(transformArray, 3);
        localVector2.set(1, 1, 1);
        localMatrix.compose(localVector, localQuaternion, localVector2).getInverse(localMatrix);
        localVector.toArray(xrState.position);
        localQuaternion.toArray(xrState.orientation);
        localMatrix.toArray(xrState.leftViewMatrix);
        xrState.leftProjectionMatrix.set(projectionArray.slice(0, 16));

        localVector.fromArray(transformArray, 3 + 4);
        localQuaternion.fromArray(transformArray, 3 + 4 + 3);
        // localVector2.set(1, 1, 1);
        localMatrix.compose(localVector, localQuaternion, localVector2).getInverse(localMatrix);
        localMatrix.toArray(xrState.rightViewMatrix);
        xrState.rightProjectionMatrix.set(projectionArray.slice(16, 32));

        let controllersArrayIndex = 0;
        {
          const leftGamepad = xrState.gamepads[0];
          leftGamepad.connected[0] = controllersArray[controllersArrayIndex];
          controllersArrayIndex++;
          leftGamepad.position.set(controllersArray.slice(controllersArrayIndex, controllersArrayIndex + 3));
          controllersArrayIndex += 3;
          leftGamepad.orientation.set(controllersArray.slice(controllersArrayIndex, controllersArrayIndex + 4));
          controllersArrayIndex += 4;
          const leftTriggerValue = controllersArray[controllersArrayIndex];
          leftGamepad.buttons[1].value[0] = leftTriggerValue;
          const leftTriggerPushed = leftTriggerValue > 0.5 ? 1 : 0;
          leftGamepad.buttons[1].touched[0] = leftTriggerPushed;
          leftGamepad.buttons[1].pressed[0] = leftTriggerPushed;
          leftGamepad.axes[2] = leftTriggerValue;
          controllersArrayIndex++;
          const leftBumperValue = controllersArray[controllersArrayIndex];
          leftGamepad.buttons[2].value[0] = leftBumperValue;
          const leftBumperPushed = leftBumperValue > 0.5 ? 1 : 0;
          leftGamepad.buttons[2].touched[0] = leftBumperPushed;
          leftGamepad.buttons[2].pressed[0] = leftBumperPushed;
          controllersArrayIndex++;
          const leftHomeValue = controllersArray[controllersArrayIndex];
          leftGamepad.buttons[3].value[0] = leftHomeValue;
          const leftHomePushed = leftHomeValue > 0.5 ? 1 : 0;
          leftGamepad.buttons[3].touched[0] = leftHomePushed;
          leftGamepad.buttons[3].pressed[0] = leftHomePushed;
          controllersArrayIndex++;
          leftGamepad.axes[0] = controllersArray[controllersArrayIndex];
          leftGamepad.axes[1] = controllersArray[controllersArrayIndex + 1];
          const leftPadValue = controllersArray[controllersArrayIndex + 2];
          leftGamepad.buttons[0].value[0] = leftPadValue;
          const leftPadTouched = leftPadValue > 0 ? 1 : 0;
          const leftPadPushed = leftPadValue > 0.5 ? 1: 0;
          leftGamepad.buttons[0].touched[0] = leftPadTouched;
          leftGamepad.buttons[0].pressed[0] = leftPadPushed;
          controllersArrayIndex += 3;
        }
        {
          const rightGamepad = xrState.gamepads[1];
          rightGamepad.connected[0] = controllersArray[controllersArrayIndex];
          controllersArrayIndex++;
          rightGamepad.position.set(controllersArray.slice(controllersArrayIndex, controllersArrayIndex + 3));
          controllersArrayIndex += 3;
          rightGamepad.orientation.set(controllersArray.slice(controllersArrayIndex, controllersArrayIndex + 4));
          controllersArrayIndex += 4;
          const rightTriggerValue = controllersArray[controllersArrayIndex];
          rightGamepad.buttons[1].value[0] = rightTriggerValue;
          const rightTriggerPushed = rightTriggerValue > 0.5 ? 1 : 0;
          rightGamepad.buttons[1].touched[0] = rightTriggerPushed;
          rightGamepad.buttons[1].pressed[0] = rightTriggerPushed;
          rightGamepad.axes[2] = rightTriggerValue;
          controllersArrayIndex++;
          const rightBumperValue = controllersArray[controllersArrayIndex];
          rightGamepad.buttons[2].value[0] = rightBumperValue;
          const rightBumperPushed = rightBumperValue > 0.5 ? 1 : 0;
          rightGamepad.buttons[2].touched[0] = rightBumperPushed;
          rightGamepad.buttons[2].pressed[0] = rightBumperPushed;
          controllersArrayIndex++;
          const rightHomeValue = controllersArray[controllersArrayIndex];
          rightGamepad.buttons[3].value[0] = rightHomeValue;
          const rightHomePushed = rightHomeValue > 0.5 ? 1 : 0;
          rightGamepad.buttons[3].touched[0] = rightHomePushed;
          rightGamepad.buttons[3].pressed[0] = rightHomePushed;
          controllersArrayIndex++;
          rightGamepad.axes[0] = controllersArray[controllersArrayIndex];
          rightGamepad.axes[1] = controllersArray[controllersArrayIndex + 1];
          const rightPadValue = controllersArray[controllersArrayIndex + 2];
          rightGamepad.buttons[0].value[0] = rightPadValue;
          const rightPadTouched = rightPadValue > 0 ? 1 : 0;
          const rightPadPushed = rightPadValue > 0.5 ? 1 : 0;
          rightGamepad.buttons[0].touched[0] = rightPadTouched;
          rightGamepad.buttons[0].pressed[0] = rightPadPushed;
          controllersArrayIndex += 3;
        }
      }

      // update magic leap state
      nativeMl.Update(mlPresentState.mlContext, mlGlContext); // gl context for mesh buffer population
      nativeMl.Poll();

      // prepare magic leap frame
      mlPresentState.mlContext.PrepareFrame(
        mlGlContext, // gl context for depth population
        mlPresentState.mlMsFbo,
        xrState.renderWidth[0]*2,
        xrState.renderHeight[0],
      );
    } else {
      /* await new Promise((accept, reject) => {
        const now = Date.now();
        const timeDiff = now - lastFrameTime;
        const waitTime = Math.max(8 - timeDiff, 0);
        setTimeout(accept, waitTime);
      }); */
    }

    // compute derived gamepads data
    for (let i = 0; i < xrState.gamepads.length; i++) {
      const gamepad = xrState.gamepads[i];
      localQuaternion.fromArray(gamepad.orientation);
      localVector
        .set(0, 0, -1)
        .applyQuaternion(localQuaternion)
        .toArray(gamepad.direction);
      localVector.fromArray(gamepad.position);
      localVector2.set(1, 1, 1);
      localMatrix
        .compose(localVector, localQuaternion, localVector2)
        .toArray(gamepad.transformMatrix);
    }

    // emit xr events
    window[symbols.mrDisplaysSymbol].xrDisplay.session && window[symbols.mrDisplaysSymbol].xrDisplay.session.update();
    window[symbols.mrDisplaysSymbol].xmDisplay.session && window[symbols.mrDisplaysSymbol].xmDisplay.session.update();
  };
  const _tickAnimationFrameSubmit = () => {
    // composite framebuffers
    for (let i = 0; i < contexts.length; i++) {
      const context = contexts[i];
      const windowHandle = context.getWindowHandle();

      const {nativeWindow} = nativeBindings;
      nativeWindow.setCurrentWindowContext(windowHandle);
      if (isMac) { // XXX move these to window internal
        context.flush();
      }

      const isVisible = nativeWindow.isVisible(windowHandle) || vrGlContext === context || mlGlContext === context;
      if (isVisible) {
        // console.log('blit layers', fakePresentState.layers.length);

        if (vrGlContext === context && vrPresentState.hasPose) {
          if (vrPresentState.layers.length > 0) {
            nativeWindow.composeLayers(context, vrPresentState.fbo, vrPresentState.layers, xrState);
          } else {
            nativeWindow.blitFrameBuffer(context, vrPresentState.msFbo, vrPresentState.fbo, vrGlContext.canvas.width, vrGlContext.canvas.height, vrGlContext.canvas.width, vrGlContext.canvas.height, true, false, false);
          }

          vrPresentState.compositor.Submit(context, vrPresentState.tex);
          vrPresentState.hasPose = false;

          nativeWindow.blitFrameBuffer(context, vrPresentState.fbo, 0, vrGlContext.canvas.width * (args.blit ? 0.5 : 1), vrGlContext.canvas.height, xrState.renderWidth[0], xrState.renderHeight[0], true, false, false);
        } else if (mlGlContext === context && mlPresentState.mlHasPose) {
          if (mlPresentState.layers.length > 0) { // TODO: composition can be directly to the output texture array
            nativeWindow.composeLayers(context, mlPresentState.mlFbo, mlPresentState.layers, xrState);
          } else {
            nativeWindow.blitFrameBuffer(context, mlPresentState.mlMsFbo, mlPresentState.mlFbo, mlGlContext.canvas.width, mlGlContext.canvas.height, mlGlContext.canvas.width, mlGlContext.canvas.height, true, false, false);
          }

          mlPresentState.mlContext.SubmitFrame(mlPresentState.mlTex, mlGlContext.canvas.width, mlGlContext.canvas.height);
          mlPresentState.mlHasPose = false;

          // nativeWindow.blitFrameBuffer(context, mlPresentState.mlFbo, 0, mlGlContext.canvas.width, mlGlContext.canvas.height, xrState.renderWidth[0], xrState.renderHeight[0], true, false, false);
        } else if (fakePresentState.layers.length > 0) { // XXX blit only to the intended context
          nativeWindow.composeLayers(context, 0, fakePresentState.layers, xrState);
        }
      }

      if (isMac) {
        context.bindFramebufferRaw(context.FRAMEBUFFER, null);
      }
      nativeWindow.swapBuffers(windowHandle); // XXX swap buffers on the child side
      if (isMac) {
        const drawFramebuffer = context.getFramebuffer(context.DRAW_FRAMEBUFFER);
        if (drawFramebuffer) {
          context.bindFramebuffer(context.DRAW_FRAMEBUFFER, drawFramebuffer);
        }

        const readFramebuffer = context.getFramebuffer(context.READ_FRAMEBUFFER);
        if (readFramebuffer) {
          context.bindFramebuffer(context.READ_FRAMEBUFFER, readFramebuffer);
        }
      }
    }
  };
  window.tickAnimationFrame = type => {
    switch (type) {
      case 'wait': return _tickAnimationFrameWait();
      case 'top': return _tickAnimationFrameTop();
      case 'child': return _tickAnimationFrameChild();
      case 'submit': return _tickAnimationFrameSubmit();
      default: throw new Error(`unknown tick animation frame mode: ${type}`);
    }
  };
  
  const _makeMrDisplays = () => {
    const _bindMRDisplay = display => {
      display.onrequestanimationframe = _makeRequestAnimationFrame(window);
      display.oncancelanimationframe = window.cancelAnimationFrame;
      display.onvrdisplaypresentchange = () => {
        process.nextTick(() => {
          const e = new Event('vrdisplaypresentchange');
          e.display = display;
          window.dispatchEvent(e);
        });
      };
    };
    
    const fakeVrDisplay = new FakeVRDisplay(window);
    fakeVrDisplay.onrequestpresent = layers => {
      if (!GlobalContext.fakePresentState.fakeVrDisplay) {
        GlobalContext.fakePresentState.fakeVrDisplay = fakeVrDisplay;
        fakeVrDisplay.waitGetPoses();
      }

      const [{source: canvas}] = layers;
      const {_context: context} = canvas;
      return {
        width: context.drawingBufferWidth,
        height: context.drawingBufferHeight,
        msFbo: null,
      };
    };
    fakeVrDisplay.onexitpresent = () => {
      GlobalContext.fakePresentState.fakeVrDisplay = null;
    };
    fakeVrDisplay.onlayers = layers => {
      GlobalContext.fakePresentState.layers = layers;
    };

    const vrDisplay = new VRDisplay('VR');
    _bindMRDisplay(vrDisplay);
    vrDisplay.onrequestpresent = layers => nativeVr.requestPresent(layers);
    vrDisplay.onexitpresent = () => nativeVr.exitPresent();
    vrDisplay.onlayers = layers => {
      GlobalContext.vrPresentState.layers = layers;
    };

    const xrDisplay = new XR.XRDevice('VR');
    xrDisplay.onrequestpresent = layers => nativeVr.requestPresent(layers);
    xrDisplay.onexitpresent = () => nativeVr.exitPresent();
    xrDisplay.onrequestanimationframe = _makeRequestAnimationFrame(window);
    xrDisplay.oncancelanimationframe = window.cancelAnimationFrame;
    xrDisplay.requestSession = (requestSession => function() {
      return requestSession.apply(this, arguments)
        .then(session => {
          vrDisplay.isPresenting = true;
          session.once('end', () => {
            vrDisplay.isPresenting = false;
          });
          return session;
        });
    })(xrDisplay.requestSession);
    xrDisplay.onlayers = layers => {
      GlobalContext.vrPresentState.layers = layers;
    };

    const mlDisplay = new VRDisplay('AR');
    _bindMRDisplay(mlDisplay);
    mlDisplay.onrequestpresent = layers => nativeMl.requestPresent(layers);
    mlDisplay.onexitpresent = () => nativeMl.exitPresent();
    mlDisplay.onrequesthittest = _makeOnRequestHitTest(window);
    mlDisplay.onlayers = layers => {
      GlobalContext.mlPresentState.layers = layers;
    };

    const xmDisplay = new XR.XRDevice('AR');
    xmDisplay.onrequestpresent = layers => nativeMl.requestPresent(layers);
    xmDisplay.onexitpresent = () => nativeMl.exitPresent();
    xmDisplay.onrequestanimationframe = _makeRequestAnimationFrame(window);
    xmDisplay.oncancelanimationframe = window.cancelAnimationFrame;
    xmDisplay.requestSession = (requestSession => function() {
      return requestSession.apply(this, arguments)
        .then(session => {
          mlDisplay.isPresenting = true;
          session.once('end', () => {
            mlDisplay.isPresenting = false;
          });
          return session;
        });
    })(xmDisplay.requestSession);
    xmDisplay.onrequesthittest = _makeOnRequestHitTest(window);
    xmDisplay.onlayers = layers => {
      GlobalContext.mlPresentState.layers = layers;
    };

    return {
      fakeVrDisplay,
      vrDisplay,
      xrDisplay,
      mlDisplay,
      xmDisplay,
    };
  };
  window[symbols.mrDisplaysSymbol] = _makeMrDisplays();

  window.document = _parseDocument(options.htmlString, window);
  window.document.hidden = options.hidden || false;
  window.document.xrOffset = options.xrOffset ? XRRigidTransform.fromJSON(options.xrOffset) : new XRRigidTransform();
})(global);

global.require = undefined;
global.process = undefined;
// global.setImmediate = undefined; // need this for the TLS implementation