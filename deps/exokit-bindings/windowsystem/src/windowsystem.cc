#include <windowsystem.h>

namespace windowsystembase {

const char *composeVsh = "\
#version 330\n\
\n\
in vec2 position;\n\
in vec2 uv;\n\
out vec2 vUv;\n\
\n\
void main() {\n\
  vUv = uv;\n\
  gl_Position = vec4(position.xy, 0., 1.);\n\
}\n\
";
const char *composeFsh = "\
#version 330\n\
\n\
in vec2 vUv;\n\
out vec4 fragColor;\n\
uniform sampler2D colorTex;\n\
uniform sampler2D depthTex;\n\
\n\
void main() {\n\
  fragColor = texture2D(colorTex, vUv);\n\
  gl_FragDepth = texture2D(depthTex, vUv).r;\n\
}\n\
";

void InitializeLocalGlState(WebGLRenderingContext *gl) {
  // compose shader
  ComposeSpec *composeSpec = new ComposeSpec();

  glGenFramebuffers(1, &composeSpec->composeReadFbo);
  glGenFramebuffers(1, &composeSpec->composeWriteFbo);

  glGenVertexArrays(1, &composeSpec->composeVao);
  glBindVertexArray(composeSpec->composeVao);

  // vertex Shader
  GLuint composeVertex = glCreateShader(GL_VERTEX_SHADER);
  glShaderSource(composeVertex, 1, &composeVsh, NULL);
  glCompileShader(composeVertex);
  GLint success;
  glGetShaderiv(composeVertex, GL_COMPILE_STATUS, &success);
  if (!success) {
    char infoLog[4096];
    GLsizei length;
    glGetShaderInfoLog(composeVertex, sizeof(infoLog), &length, infoLog);
    infoLog[length] = '\0';
    std::cout << "ML compose vertex shader compilation failed:\n" << infoLog << std::endl;
    return;
  };

  // fragment Shader
  GLuint composeFragment = glCreateShader(GL_FRAGMENT_SHADER);
  glShaderSource(composeFragment, 1, &composeFsh, NULL);
  glCompileShader(composeFragment);
  glGetShaderiv(composeFragment, GL_COMPILE_STATUS, &success);
  if (!success) {
    char infoLog[4096];
    GLsizei length;
    glGetShaderInfoLog(composeFragment, sizeof(infoLog), &length, infoLog);
    infoLog[length] = '\0';
    std::cout << "ML compose fragment shader compilation failed:\n" << infoLog << std::endl;
    return;
  };

  // shader Program
  composeSpec->composeProgram = glCreateProgram();
  glAttachShader(composeSpec->composeProgram, composeVertex);
  glAttachShader(composeSpec->composeProgram, composeFragment);
  glLinkProgram(composeSpec->composeProgram);
  glGetProgramiv(composeSpec->composeProgram, GL_LINK_STATUS, &success);
  if (!success) {
    char infoLog[4096];
    GLsizei length;
    glGetShaderInfoLog(composeSpec->composeProgram, sizeof(infoLog), &length, infoLog);
    infoLog[length] = '\0';
    std::cout << "ML compose program linking failed\n" << infoLog << std::endl;
    return;
  }

  composeSpec->positionLocation = glGetAttribLocation(composeSpec->composeProgram, "position");
  if (composeSpec->positionLocation == -1) {
    std::cout << "ML compose program failed to get attrib location for 'position'" << std::endl;
    return;
  }
  composeSpec->uvLocation = glGetAttribLocation(composeSpec->composeProgram, "uv");
  if (composeSpec->uvLocation == -1) {
    std::cout << "ML compose program failed to get attrib location for 'uv'" << std::endl;
    return;
  }
  composeSpec->colorTexLocation = glGetUniformLocation(composeSpec->composeProgram, "colorTex");
  if (composeSpec->colorTexLocation == -1) {
    std::cout << "ML compose program failed to get uniform location for 'colorTex'" << std::endl;
    return;
  }
  composeSpec->depthTexLocation = glGetUniformLocation(composeSpec->composeProgram, "depthTex");
  if (composeSpec->depthTexLocation == -1) {
    std::cout << "ML compose program failed to get uniform location for 'depthTex'" << std::endl;
    return;
  }

  // delete the shaders as they're linked into our program now and no longer necessery
  glDeleteShader(composeVertex);
  glDeleteShader(composeFragment);

  glGenBuffers(1, &composeSpec->positionBuffer);
  glBindBuffer(GL_ARRAY_BUFFER, composeSpec->positionBuffer);
  static const float positions[] = {
    -1.0f, 1.0f,
    1.0f, 1.0f,
    -1.0f, -1.0f,
    1.0f, -1.0f,
  };
  glBufferData(GL_ARRAY_BUFFER, sizeof(positions), positions, GL_STATIC_DRAW);
  glEnableVertexAttribArray(composeSpec->positionLocation);
  glVertexAttribPointer(composeSpec->positionLocation, 2, GL_FLOAT, false, 0, 0);

  glGenBuffers(1, &composeSpec->uvBuffer);
  glBindBuffer(GL_ARRAY_BUFFER, composeSpec->uvBuffer);
  static const float uvs[] = {
    0.0f, 1.0f,
    1.0f, 1.0f,
    0.0f, 0.0f,
    1.0f, 0.0f,
  };
  glBufferData(GL_ARRAY_BUFFER, sizeof(uvs), uvs, GL_STATIC_DRAW);
  glEnableVertexAttribArray(composeSpec->uvLocation);
  glVertexAttribPointer(composeSpec->uvLocation, 2, GL_FLOAT, false, 0, 0);

  glGenBuffers(1, &composeSpec->indexBuffer);
  static const uint16_t indices[] = {0, 2, 1, 2, 3, 1};
  glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, composeSpec->indexBuffer);
  glBufferData(GL_ELEMENT_ARRAY_BUFFER, sizeof(indices), indices, GL_STATIC_DRAW);

  gl->keys[GlKey::GL_KEY_COMPOSE] = composeSpec;

  if (gl->HasVertexArrayBinding()) {
    glBindVertexArray(gl->GetVertexArrayBinding());
  } else {
    glBindVertexArray(gl->defaultVao);
  }
  if (gl->HasBufferBinding(GL_ARRAY_BUFFER)) {
    glBindBuffer(GL_ARRAY_BUFFER, gl->GetBufferBinding(GL_ARRAY_BUFFER));
  } else {
    glBindBuffer(GL_ARRAY_BUFFER, 0);
  }
}

NAN_METHOD(CreateRenderTarget) {
  WebGLRenderingContext *gl = ObjectWrap::Unwrap<WebGLRenderingContext>(Local<Object>::Cast(info[0]));
  int width = info[1]->Uint32Value();
  int height = info[2]->Uint32Value();
  GLuint sharedColorTex = info[3]->Uint32Value();
  GLuint sharedDepthStencilTex = info[4]->Uint32Value();
  GLuint sharedMsColorTex = info[5]->Uint32Value();
  GLuint sharedMsDepthStencilTex = info[6]->Uint32Value();

  GLuint fbo;
  GLuint colorTex;
  GLuint depthStencilTex;
  GLuint msFbo;
  GLuint msColorTex;
  GLuint msDepthStencilTex;
  bool ok = CreateRenderTarget(gl, width, height, sharedColorTex, sharedDepthStencilTex, sharedMsColorTex, sharedMsDepthStencilTex, &fbo, &colorTex, &depthStencilTex, &msFbo, &msColorTex, &msDepthStencilTex);

  Local<Value> result;
  if (ok) {
    Local<Array> array = Array::New(Isolate::GetCurrent(), 6);
    array->Set(0, JS_NUM(fbo));
    array->Set(1, JS_NUM(colorTex));
    array->Set(2, JS_NUM(depthStencilTex));
    array->Set(3, JS_NUM(msFbo));
    array->Set(4, JS_NUM(msColorTex));
    array->Set(5, JS_NUM(msDepthStencilTex));
    result = array;
  } else {
    result = Null(Isolate::GetCurrent());
  }
  info.GetReturnValue().Set(result);
}

NAN_METHOD(ResizeRenderTarget) {
  WebGLRenderingContext *gl = ObjectWrap::Unwrap<WebGLRenderingContext>(Local<Object>::Cast(info[0]));
  int width = info[1]->Uint32Value();
  int height = info[2]->Uint32Value();
  GLuint fbo = info[3]->Uint32Value();
  GLuint colorTex = info[4]->Uint32Value();
  GLuint depthStencilTex = info[5]->Uint32Value();
  GLuint msFbo = info[6]->Uint32Value();
  GLuint msColorTex = info[7]->Uint32Value();
  GLuint msDepthStencilTex = info[8]->Uint32Value();

  const int samples = 4;

  /* {
    glBindFramebuffer(GL_DRAW_FRAMEBUFFER, msFbo);

    glBindTexture(GL_TEXTURE_2D_MULTISAMPLE, msDepthStencilTex);
    glTexParameteri(GL_TEXTURE_2D_MULTISAMPLE, GL_TEXTURE_MAX_LEVEL, 0);
    glTexStorage2DMultisample(GL_TEXTURE_2D_MULTISAMPLE, samples, GL_DEPTH24_STENCIL8, width, height, true);
    glFramebufferTexture2D(GL_DRAW_FRAMEBUFFER, GL_DEPTH_STENCIL_ATTACHMENT, GL_TEXTURE_2D_MULTISAMPLE, msDepthStencilTex, 0);

    glBindTexture(GL_TEXTURE_2D_MULTISAMPLE, msColorTex);
    glTexParameteri(GL_TEXTURE_2D_MULTISAMPLE, GL_TEXTURE_MAX_LEVEL, 0);
    glTexStorage2DMultisample(GL_TEXTURE_2D_MULTISAMPLE, samples, GL_RGBA8, width, height, true);
    glFramebufferTexture2D(GL_DRAW_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D_MULTISAMPLE, msColorTex, 0);
  } */
  {
    glBindFramebuffer(GL_DRAW_FRAMEBUFFER, fbo);

    glBindTexture(GL_TEXTURE_2D, depthStencilTex);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAX_LEVEL, 0);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_DEPTH24_STENCIL8, width, height, 0, GL_DEPTH_STENCIL, GL_UNSIGNED_INT_24_8, nullptr);
    glFramebufferTexture2D(GL_DRAW_FRAMEBUFFER, GL_DEPTH_STENCIL_ATTACHMENT, GL_TEXTURE_2D, depthStencilTex, 0);

    glBindTexture(GL_TEXTURE_2D, colorTex);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAX_LEVEL, 0);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA8, width, height, 0, GL_RGBA, GL_UNSIGNED_BYTE, nullptr);
    glFramebufferTexture2D(GL_DRAW_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, colorTex, 0);
  }

  if (gl->HasFramebufferBinding(GL_DRAW_FRAMEBUFFER)) {
    glBindFramebuffer(GL_DRAW_FRAMEBUFFER, gl->GetFramebufferBinding(GL_DRAW_FRAMEBUFFER));
  } else {
    glBindFramebuffer(GL_DRAW_FRAMEBUFFER, gl->defaultFramebuffer);
  }
  if (gl->HasTextureBinding(gl->activeTexture, GL_TEXTURE_2D)) {
    glBindTexture(GL_TEXTURE_2D, gl->GetTextureBinding(gl->activeTexture, GL_TEXTURE_2D));
  } else {
    glBindTexture(GL_TEXTURE_2D, 0);
  }
  if (gl->HasTextureBinding(gl->activeTexture, GL_TEXTURE_2D_MULTISAMPLE)) {
    glBindTexture(GL_TEXTURE_2D_MULTISAMPLE, gl->GetTextureBinding(gl->activeTexture, GL_TEXTURE_2D_MULTISAMPLE));
  } else {
    glBindTexture(GL_TEXTURE_2D_MULTISAMPLE, 0);
  }
  if (gl->HasTextureBinding(gl->activeTexture, GL_TEXTURE_CUBE_MAP)) {
    glBindTexture(GL_TEXTURE_CUBE_MAP, gl->GetTextureBinding(gl->activeTexture, GL_TEXTURE_CUBE_MAP));
  } else {
    glBindTexture(GL_TEXTURE_CUBE_MAP, 0);
  }
}

NAN_METHOD(DestroyRenderTarget) {
  if (info[0]->IsNumber() && info[1]->IsNumber() && info[2]->IsNumber()) {
    GLuint fbo = info[0]->Uint32Value();
    GLuint tex = info[1]->Uint32Value();
    GLuint depthTex = info[2]->Uint32Value();

    glDeleteFramebuffers(1, &fbo);
    glDeleteTextures(1, &tex);
    glDeleteTextures(1, &depthTex);
  } else {
    Nan::ThrowError("DestroyRenderTarget: invalid arguments");
  }
}

void ComposeLayer(ComposeSpec *composeSpec, const LayerSpec &layer) {
  glActiveTexture(GL_TEXTURE0);
  glBindTexture(GL_TEXTURE_2D, layer.colorTex);
  glUniform1i(composeSpec->colorTexLocation, 0);

  glActiveTexture(GL_TEXTURE1);
  glBindTexture(GL_TEXTURE_2D, layer.depthTex);
  glUniform1i(composeSpec->depthTexLocation, 1);

  glViewport(0, 0, layer.width, layer.height);
  // glScissor(0, 0, width, height);
  glDrawElements(GL_TRIANGLES, 6, GL_UNSIGNED_SHORT, 0);
}

void ComposeLayers(WebGLRenderingContext *gl, int width, int height, const std::vector<LayerSpec> &layers) {
  ComposeSpec *composeSpec = (ComposeSpec *)(gl->keys[GlKey::GL_KEY_COMPOSE]);

  glBindFramebuffer(GL_DRAW_FRAMEBUFFER, gl->defaultFramebuffer);
  glBindVertexArray(composeSpec->composeVao);
  glUseProgram(composeSpec->composeProgram);

  glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT|GL_STENCIL_BUFFER_BIT);

  // blit
  for (size_t i = 0; i < layers.size(); i++) {
    const LayerSpec &layer = layers[i];

    if (layer.blit) {
      glBindFramebuffer(GL_READ_FRAMEBUFFER, composeSpec->composeReadFbo);
      glFramebufferTexture2D(GL_READ_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D_MULTISAMPLE, layer.msColorTex, 0);
      glFramebufferTexture2D(GL_READ_FRAMEBUFFER, GL_DEPTH_STENCIL_ATTACHMENT, GL_TEXTURE_2D_MULTISAMPLE, layer.msDepthTex, 0);

      glBindFramebuffer(GL_DRAW_FRAMEBUFFER, composeSpec->composeWriteFbo);
      glFramebufferTexture2D(GL_DRAW_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, layer.colorTex, 0);
      glFramebufferTexture2D(GL_DRAW_FRAMEBUFFER, GL_DEPTH_STENCIL_ATTACHMENT, GL_TEXTURE_2D, layer.depthTex, 0);

      glBlitFramebuffer(
        0, 0,
        layer.width, layer.height,
        0, 0,
        layer.width, layer.height,
        GL_COLOR_BUFFER_BIT,
        GL_LINEAR);

      glBlitFramebuffer(
        0, 0,
        layer.width, layer.height,
        0, 0,
        layer.width, layer.height,
        GL_DEPTH_BUFFER_BIT | GL_STENCIL_BUFFER_BIT,
        GL_NEAREST);

      glBindFramebuffer(GL_DRAW_FRAMEBUFFER, gl->defaultFramebuffer);
    }
  }

  // render unblitted
  for (size_t i = 0; i < layers.size(); i++) {
    const LayerSpec &layer = layers[i];

    if (!layer.blit) {
      ComposeLayer(composeSpec, layer);
    }
  }

  // render blitted
  for (size_t i = 0; i < layers.size(); i++) {
    const LayerSpec &layer = layers[i];

    if (layer.blit) {
      ComposeLayer(composeSpec, layer);
    }
  }

  if (gl->HasFramebufferBinding(GL_READ_FRAMEBUFFER)) {
    glBindFramebuffer(GL_READ_FRAMEBUFFER, gl->GetFramebufferBinding(GL_READ_FRAMEBUFFER));
  } else {
    glBindFramebuffer(GL_READ_FRAMEBUFFER, gl->defaultFramebuffer);
  }
  if (gl->HasFramebufferBinding(GL_DRAW_FRAMEBUFFER)) {
    glBindFramebuffer(GL_DRAW_FRAMEBUFFER, gl->GetFramebufferBinding(GL_DRAW_FRAMEBUFFER));
  } else {
    glBindFramebuffer(GL_DRAW_FRAMEBUFFER, gl->defaultFramebuffer);
  }
  if (gl->HasVertexArrayBinding()) {
    glBindVertexArray(gl->GetVertexArrayBinding());
  } else {
    glBindVertexArray(gl->defaultVao);
  }
  if (gl->HasProgramBinding()) {
    glUseProgram(gl->GetProgramBinding());
  } else {
    glUseProgram(0);
  }
  if (gl->viewportState.valid) {
    glViewport(gl->viewportState.x, gl->viewportState.y, gl->viewportState.w, gl->viewportState.h);
  } else {
    glViewport(0, 0, 1280, 1024);
  }
  glActiveTexture(GL_TEXTURE0);
  if (gl->HasTextureBinding(GL_TEXTURE0, GL_TEXTURE_2D)) {
    glBindTexture(GL_TEXTURE_2D, gl->GetTextureBinding(GL_TEXTURE0, GL_TEXTURE_2D));
  } else {
    glBindTexture(GL_TEXTURE_2D, 0);
  }
  glActiveTexture(GL_TEXTURE1);
  if (gl->HasTextureBinding(GL_TEXTURE1, GL_TEXTURE_2D)) {
    glBindTexture(GL_TEXTURE_2D, gl->GetTextureBinding(GL_TEXTURE1, GL_TEXTURE_2D));
  } else {
    glBindTexture(GL_TEXTURE_2D, 0);
  }
  glActiveTexture(gl->activeTexture);
}

NAN_METHOD(ComposeLayers) {
  if (info[0]->IsObject() && info[1]->IsArray()) {
    WebGLRenderingContext *gl = ObjectWrap::Unwrap<WebGLRenderingContext>(Local<Object>::Cast(info[0]));
    Local<Array> array = Local<Array>::Cast(info[1]);

    std::vector<LayerSpec> layers;
    layers.reserve(8);
    for (size_t i = 0, size = array->Length(); i < size; i++) {
      Local<Value> element = array->Get(i);

      if (element->IsObject()) {
        Local<Object> elementObj = Local<Object>::Cast(element);

        if (
          elementObj->Get(JS_STR("constructor"))->ToObject()->Get(JS_STR("name"))->StrictEquals(JS_STR("HTMLIFrameElement"))
        ) {
          if (
            elementObj->Get(JS_STR("contentDocument"))->IsObject() &&
            elementObj->Get(JS_STR("contentDocument"))->ToObject()->Get(JS_STR("framebuffer"))->IsObject()
          ) {
            Local<Object> framebufferObj = Local<Object>::Cast(elementObj->Get(JS_STR("contentDocument"))->ToObject()->Get(JS_STR("framebuffer")));
            GLuint colorTex = framebufferObj->Get(JS_STR("colorTex"))->Uint32Value();
            GLuint depthTex = framebufferObj->Get(JS_STR("depthTex"))->Uint32Value();
            GLuint msColorTex = framebufferObj->Get(JS_STR("msColorTex"))->Uint32Value();
            GLuint msDepthTex = framebufferObj->Get(JS_STR("msDepthTex"))->Uint32Value();
            int width = framebufferObj->Get(JS_STR("canvas"))->ToObject()->Get(JS_STR("width"))->Int32Value();
            int height = framebufferObj->Get(JS_STR("canvas"))->ToObject()->Get(JS_STR("height"))->Int32Value();

            layers.push_back(LayerSpec{
              width,
              height,
              msColorTex,
              msDepthTex,
              colorTex,
              depthTex,
              true
            });
          } else { // iframe not ready
            // nothing
          }
        } else {
          Local<Value> widthVal = elementObj->Get(JS_STR("width"));
          Local<Value> heightVal = elementObj->Get(JS_STR("height"));
          Local<Value> colorTexVal = elementObj->Get(JS_STR("colorTex"));
          Local<Value> depthTexVal = elementObj->Get(JS_STR("depthTex"));

          if (
            widthVal->IsNumber() &&
            heightVal->IsNumber() &&
            colorTexVal->IsObject() && colorTexVal->ToObject()->Get(JS_STR("id"))->IsNumber() &&
            depthTexVal->IsObject() && depthTexVal->ToObject()->Get(JS_STR("id"))->IsNumber()
          ) {
            int width = widthVal->Int32Value();
            int width = heightVal->Int32Value();
            GLuint colorTex = colorTexVal->ToObject()->Get(JS_STR("id"))->Uint32Value();
            GLuint depthTex = depthTexVal->ToObject()->Get(JS_STR("id"))->Uint32Value();

            layers.push_back(LayerSpec{
              width,
              height,
              0,
              0,
              colorTex,
              depthTex,
              false
            });
          } else {
            /* String::Utf8Value utf8Value(elementObj->Get(JS_STR("constructor"))->ToObject()->Get(JS_STR("name")));
            std::cout << "fail " << colorTexVal->IsObject() << " " << (colorTexVal->IsObject() && colorTexVal->ToObject()->Get(JS_STR("id"))->IsNumber()) << " " << *utf8Value << " " <<
              elementObj->Get(JS_STR("contentDocument"))->IsObject() << " " <<
              elementObj->Get(JS_STR("contentDocument"))->ToObject()->Get(JS_STR("framebuffer"))->IsObject() << " " <<
              std::endl; */
            return Nan::ThrowError("WindowSystem::ComposeLayers: invalid layer object properties");
          }
        }
      } else {
        return Nan::ThrowError("WindowSystem::ComposeLayers: invalid layer object");
      }
    }

    if (layers.size() > 0) {
      ComposeLayers(gl, layers);
    }
  } else {
    Nan::ThrowError("WindowSystem::ComposeLayers: invalid arguments");
  }
}

void Decorate(Local<Object> target) {
  Nan::SetMethod(target, "createRenderTarget", CreateRenderTarget);
  Nan::SetMethod(target, "resizeRenderTarget", ResizeRenderTarget);
  Nan::SetMethod(target, "destroyRenderTarget", DestroyRenderTarget);
  Nan::SetMethod(target, "composeLayers", ComposeLayers);
}

}
