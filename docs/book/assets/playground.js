// Inline playground for .leanmini scripts, backed by the MiniLean4 kernel
// compiled to WebAssembly. Markup expected:
//   <div class="playground"><pre>...script...</pre></div>
// The optional global window.MINILEAN_WASM_URL overrides the wasm location.
(function () {
  'use strict';

  var wasmPromise = null;

  function loadWasm() {
    if (wasmPromise) return wasmPromise;
    var url = window.MINILEAN_WASM_URL || 'assets/minilean.wasm';
    wasmPromise = fetch(url)
      .then(function (r) {
        if (!r.ok) throw new Error('HTTP ' + r.status + ' while fetching ' + url);
        return r.arrayBuffer();
      })
      .then(function (bytes) { return WebAssembly.instantiate(bytes, {}); })
      .then(function (res) { return res.instance.exports; });
    return wasmPromise;
  }

  function runScript(exports, script) {
    var enc = new TextEncoder().encode(script);
    var ptr = exports.alloc(enc.length);
    new Uint8Array(exports.memory.buffer, ptr, enc.length).set(enc);
    exports.run_script(ptr, enc.length);
    exports.dealloc(ptr, enc.length);
    var len = exports.result_len();
    var out = new Uint8Array(exports.memory.buffer, exports.result_ptr(), len);
    return new TextDecoder().decode(out);
  }

  // Generic call into an exported function that takes a UTF-8 buffer and
  // leaves its result in the shared result buffer (run_script, explore).
  function callText(exports, name, text) {
    var enc = new TextEncoder().encode(text);
    var ptr = exports.alloc(enc.length);
    new Uint8Array(exports.memory.buffer, ptr, enc.length).set(enc);
    exports[name](ptr, enc.length);
    exports.dealloc(ptr, enc.length);
    var len = exports.result_len();
    var out = new Uint8Array(exports.memory.buffer, exports.result_ptr(), len);
    return new TextDecoder().decode(out);
  }

  // Shared with explorers.js.
  window.MiniLean = {
    load: loadWasm,
    run: function (script) { return loadWasm().then(function (ex) { return runScript(ex, script); }); },
    explore: function (request) {
      return loadWasm().then(function (ex) { return JSON.parse(callText(ex, 'explore', request)); });
    },
    highlight: null // set below once the highlighter is defined
  };

  function autosize(ta) {
    ta.style.height = 'auto';
    ta.style.height = (ta.scrollHeight + 4) + 'px';
  }

  // Syntax colouring for leanmini, mirroring the build-time highlighter.
  var KEYWORDS = {};
  ('inductive where def axiom recursor goal intro induction exact apply change rw rfl qed show ' +
   'fun forall Sort index end quit').split(' ').forEach(function (k) { KEYWORDS[k] = true; });

  function escapeHtml(t) {
    return t.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }

  function highlight(src) {
    var out = '';
    var re = /(#[^\n]*)|([A-Za-z_][A-Za-z0-9_.']*)|(->|=>|[():,])|([^\n])|(\n)/g;
    var m;
    while ((m = re.exec(src)) !== null) {
      if (m[1] !== undefined) out += '<span class="c">' + escapeHtml(m[1]) + '</span>';
      else if (m[2] !== undefined) {
        if (KEYWORDS[m[2]]) out += '<span class="k">' + m[2] + '</span>';
        else if (m[2].indexOf('.') >= 0) out += '<span class="n">' + escapeHtml(m[2]) + '</span>';
        else out += escapeHtml(m[2]);
      }
      else if (m[3] !== undefined) out += '<span class="o">' + escapeHtml(m[3]) + '</span>';
      else if (m[4] !== undefined) out += escapeHtml(m[4]);
      else out += '\n';
    }
    // A trailing newline needs a visible line so the overlay keeps the textarea's height.
    if (src.endsWith('\n')) out += ' ';
    return out;
  }

  window.MiniLean.highlight = highlight;

  function setup(box) {
    var src = box.querySelector('pre, textarea');
    var initial = src ? src.textContent.replace(/^\n+/, '').replace(/\s+$/, '') : '';
    var fallback = box.getAttribute('data-file') || 'examples/your-script.leanmini';
    box.innerHTML = '';

    var wrap = document.createElement('div');
    wrap.className = 'playground-editor-wrap';
    var layer = document.createElement('pre');
    layer.className = 'playground-highlight';
    layer.setAttribute('aria-hidden', 'true');
    var editor = document.createElement('textarea');
    editor.className = 'playground-editor';
    editor.spellcheck = false;
    editor.setAttribute('autocapitalize', 'off');
    editor.setAttribute('autocorrect', 'off');
    editor.value = initial;
    editor.rows = Math.max(3, initial.split('\n').length);
    function paint() { layer.innerHTML = highlight(editor.value); }
    wrap.appendChild(layer);
    wrap.appendChild(editor);

    var bar = document.createElement('div');
    bar.className = 'playground-bar';
    var run = document.createElement('button');
    run.className = 'playground-run';
    run.type = 'button';
    run.textContent = 'run';
    run.title = 'Run (Ctrl+Enter)';
    var reset = document.createElement('button');
    reset.className = 'playground-reset';
    reset.type = 'button';
    reset.textContent = 'reset';
    bar.appendChild(run);
    bar.appendChild(reset);

    var output = document.createElement('pre');
    output.className = 'playground-output';
    output.hidden = true;

    box.appendChild(wrap);
    box.appendChild(bar);
    box.appendChild(output);

    // Renders the transcript with shell-like colours: prompts, errors, success.
    function show(text, isError) {
      output.hidden = false;
      output.textContent = '';
      var lines = text.split('\n');
      for (var i = 0; i < lines.length; i++) {
        var line = lines[i];
        var span = document.createElement('span');
        if (/^> /.test(line)) span.className = 'p';
        else if (/^(error|type mismatch|line \d+:)/.test(line) || /^[a-z].*(mismatch|exhausted|unknown|expected|cannot|not )/.test(line) && !/^(defined|added|generated|inductive)/.test(line)) span.className = 'err';
        else if (/^(QED|No goals)/.test(line)) span.className = 'ok';
        else if (/^(defined|added axiom|generated|inductive .* registered)/.test(line)) span.className = 'dim';
        else if (/^\s+\u22a2 /.test(line)) span.className = 'pw';
        span.textContent = line;
        output.appendChild(span);
        if (i < lines.length - 1) output.appendChild(document.createTextNode('\n'));
      }
      output.classList.toggle('playground-error', !!isError);
    }

    function execute() {
      run.disabled = true;
      show('running...', false);
      loadWasm()
        .then(function (exports) {
          var text = runScript(exports, editor.value);
          show(text, /(^|\n)error/.test(text));
        })
        .catch(function (err) {
          show(
            'The in-browser kernel could not be loaded (' + err.message + ').\n' +
            'Run this script from the command line instead:\n\n' +
            '  cargo run -- ' + fallback,
            true
          );
        })
        .then(function () { run.disabled = false; });
    }

    run.addEventListener('click', execute);
    reset.addEventListener('click', function () {
      editor.value = initial;
      autosize(editor);
      paint();
      output.hidden = true;
      output.textContent = '';
    });
    editor.addEventListener('input', function () { autosize(editor); paint(); });
    editor.addEventListener('scroll', function () { layer.scrollTop = editor.scrollTop; layer.scrollLeft = editor.scrollLeft; });
    editor.addEventListener('keydown', function (e) {
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        execute();
      }
    });
    autosize(editor);
    paint();
  }

  function init() {
    var boxes = document.querySelectorAll('div.playground');
    for (var i = 0; i < boxes.length; i++) setup(boxes[i]);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
