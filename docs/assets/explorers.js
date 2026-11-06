// Live explorers for the MiniLean4 ebook. Each <div class="explorer" data-kind="...">
// is turned into an interactive view backed by the kernel compiled to
// WebAssembly (window.MiniLean from playground.js). Kinds:
//   ast        data-term                        syntax tree of a term
//   derive     data-term [data-ctx]             typing derivation
//   reduce     data-term [data-ctx]             head reduction, step by step
//   scope      data-term                        binders and the variables they bind
//   subst      data-term data-var data-with     naive vs capture-avoiding substitution
//   proof      <pre class="script">             synchronized script / goals / proof term
//   ctree      data-term                        a value as a tree of constructors
//   universes  (no kernel)                      the imax rule on the universe ladder
// A child <pre class="prelude"> supplies definitions that the term may use.
(function () {
  'use strict';

  var HUES = 6;
  var I18N = (window.MINILEAN_I18N && window.MINILEAN_I18N.js) || {};
  var DEFAULTS = {
    imax_prop: 'B is a proposition, so the whole \u03a0 is a proposition no matter what it quantifies over: imax({u}, 0) = 0. This is impredicativity.',
    imax_pred: 'B is not a proposition, so the \u03a0 lives in the larger of the two universes: imax({u}, {v}) = max({u}, {v}) = {r}. This is predicativity.'
  };
  function t(key) { return I18N[key] || DEFAULTS[key] || key; }

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  function attr(box, name, fallback) {
    var v = box.getAttribute('data-' + name);
    return v === null ? fallback : v;
  }

  function childText(box, cls) {
    var pre = box.querySelector('pre.' + cls);
    if (!pre) return '';
    return pre.textContent.replace(/^\n+/, '').replace(/\s+$/, '');
  }

  // ----- Tokens -----

  function renderTokens(container, tokens, opts) {
    opts = opts || {};
    container.innerHTML = '';
    container.classList.add('tokens');
    var group = null; // consecutive marked tokens share one highlight box
    tokens.forEach(function (t) {
      var s = el('span', 'tk tk-' + t.k, t.t);
      if ((t.k === 'binder' || t.k === 'bound') && t.id >= 0) {
        s.classList.add('tk-b' + (t.id % HUES));
        s.setAttribute('data-bind', String(t.id));
      }
      if (t.k === 'hole') {
        s.setAttribute('data-hole', String(t.id));
        if (opts.currentHole !== undefined && t.id === opts.currentHole) s.classList.add('tk-current');
      }
      if (t.m) {
        if (!group) { group = el('span', 'tk-mark'); container.appendChild(group); }
        group.appendChild(s);
      } else {
        group = null;
        container.appendChild(s);
      }
    });
    // Hovering a binder or a bound occurrence lights up the whole group.
    container.addEventListener('mouseover', function (e) {
      var id = e.target.getAttribute && e.target.getAttribute('data-bind');
      container.querySelectorAll('.tk-hl').forEach(function (x) { x.classList.remove('tk-hl'); });
      if (id === null || id === undefined) return;
      container.querySelectorAll('[data-bind="' + id + '"]').forEach(function (x) { x.classList.add('tk-hl'); });
    });
    container.addEventListener('mouseleave', function () {
      container.querySelectorAll('.tk-hl').forEach(function (x) { x.classList.remove('tk-hl'); });
    });
    return container;
  }

  // ----- Frame shared by all explorers -----

  function frame(box, title, inputs) {
    box.innerHTML = '';
    var bar = el('div', 'ex-bar');
    bar.appendChild(el('span', 'ex-title', title));
    var status = el('span', 'ex-status', '');
    bar.appendChild(status);
    box.appendChild(bar);
    var form = el('form', 'ex-inputs');
    var fields = {};
    inputs.forEach(function (spec) {
      var label = el('label', 'ex-field');
      label.appendChild(el('span', 'ex-label', spec.label));
      var input = el('input', 'ex-input');
      input.type = 'text';
      input.value = spec.value || '';
      input.spellcheck = false;
      input.setAttribute('autocapitalize', 'off');
      if (spec.wide) label.classList.add('wide');
      label.appendChild(input);
      form.appendChild(label);
      fields[spec.name] = input;
    });
    var go = el('button', 'ex-go', t('update'));
    go.type = 'submit';
    form.appendChild(go);
    box.appendChild(form);
    var body = el('div', 'ex-body');
    box.appendChild(body);
    var err = el('div', 'ex-error');
    err.hidden = true;
    box.appendChild(err);
    return {
      fields: fields, body: body, form: form, status: status,
      error: function (msg) { err.hidden = !msg; err.textContent = msg || ''; },
      busy: function (on) { status.textContent = on ? t('thinking') : ''; }
    };
  }

  function request(op, args, tail) {
    var lines = [op].concat(args || []);
    var text = lines.join('\n');
    if (tail) text += '\n---\n' + tail;
    return window.MiniLean.explore(text);
  }

  function failLoad(ui, err) {
    ui.error(t('The in-browser kernel could not be loaded') + ' (' + err.message + ').');
  }

  // ----- ast -----

  function astNode(n) {
    var li = el('li', 'ast-node ast-' + n.kind);
    var head = el('span', 'ast-head');
    head.appendChild(el('span', 'ast-kind', n.kind));
    if (n.label) head.appendChild(el('span', 'ast-label', n.label));
    head.title = n.pretty;
    li.appendChild(head);
    if (n.children.length) {
      var ul = el('ul', '');
      n.children.forEach(function (c) { ul.appendChild(astNode(c)); });
      li.appendChild(ul);
    }
    return li;
  }

  function setupAst(box) {
    var prelude = childText(box, 'prelude');
    var ui = frame(box, t('syntax tree'), [{ name: 'term', label: t('term'), value: attr(box, 'term', ''), wide: true }]);
    var picked = el('div', 'ex-picked');
    function run() {
      ui.busy(true);
      request('ast', [ui.fields.term.value], prelude).then(function (j) {
        ui.busy(false);
        if (j.error) { ui.error(j.error); return; }
        ui.error('');
        ui.body.innerHTML = '';
        var tokens = renderTokens(el('div', 'ex-term'), j.tokens);
        ui.body.appendChild(tokens);
        var tree = el('ul', 'ast');
        tree.appendChild(astNode(j.ast));
        ui.body.appendChild(tree);
        picked.textContent = t('click a node to see the subterm it stands for');
        ui.body.appendChild(picked);
        tree.addEventListener('click', function (e) {
          var head = e.target.closest('.ast-head');
          if (!head) return;
          tree.querySelectorAll('.ast-head.on').forEach(function (x) { x.classList.remove('on'); });
          head.classList.add('on');
          picked.textContent = head.title;
        });
      }).catch(function (e) { ui.busy(false); failLoad(ui, e); });
    }
    ui.form.addEventListener('submit', function (e) { e.preventDefault(); run(); });
    run();
  }

  // ----- derive -----

  function judgment(n) {
    var j = el('span', 'dv-judgment');
    var ctx = n.ctx.map(function (h) { return h.name + ' : ' + h.type; }).join(', ');
    j.appendChild(el('span', 'dv-ctx', ctx || '·'));
    j.appendChild(el('span', 'dv-turnstile', ' ⊢ '));
    j.appendChild(el('span', 'dv-term', n.term));
    j.appendChild(el('span', 'dv-colon', n.ok ? ' : ' : '  '));
    j.appendChild(el('span', n.ok ? 'dv-type' : 'dv-fail', n.ok ? n.result : '✗ ' + n.result));
    return j;
  }

  function deriveList(n, depth) {
    var li = el('li', 'dv-item' + (n.ok ? '' : ' fail'));
    var row = el('div', 'dv-row');
    if (n.premise) row.appendChild(el('span', 'dv-premise', n.premise));
    row.appendChild(judgment(n));
    row.appendChild(el('span', 'dv-rule', n.rule));
    li.appendChild(row);
    if (n.note) li.appendChild(el('div', 'dv-note', n.note));
    if (n.children.length) {
      var ul = el('ul', '');
      n.children.forEach(function (c) { ul.appendChild(deriveList(c, depth + 1)); });
      li.appendChild(ul);
      var toggle = el('button', 'trace-toggle', 'hide ' + n.children.length);
      toggle.type = 'button';
      toggle.addEventListener('click', function () {
        var c = li.classList.toggle('collapsed');
        toggle.textContent = (c ? 'show ' : 'hide ') + n.children.length;
      });
      row.appendChild(toggle);
    }
    return li;
  }

  function deriveTree(n) {
    var node = el('div', 'dv-node' + (n.ok ? '' : ' fail'));
    if (n.children.length) {
      var prem = el('div', 'dv-premises');
      n.children.forEach(function (c) { prem.appendChild(deriveTree(c)); });
      node.appendChild(prem);
    }
    var line = el('div', 'dv-line');
    line.appendChild(el('span', 'dv-rule', n.rule));
    node.appendChild(line);
    var concl = el('div', 'dv-conclusion');
    concl.appendChild(judgment(n));
    if (n.note) concl.title = n.note;
    node.appendChild(concl);
    return node;
  }

  function setupDerive(box) {
    var prelude = childText(box, 'prelude');
    var inputs = [{ name: 'term', label: t('term'), value: attr(box, 'term', ''), wide: true }];
    inputs.push({ name: 'ctx', label: t('context'), value: attr(box, 'ctx', '') });
    var ui = frame(box, t('typing derivation'), inputs);
    var asTree = attr(box, 'view', 'list') === 'tree';
    function run() {
      ui.busy(true);
      request('derive', [ui.fields.term.value, ui.fields.ctx.value], prelude).then(function (j) {
        ui.busy(false);
        if (j.error) { ui.error(j.error); return; }
        ui.error('');
        ui.body.innerHTML = '';
        var modes = el('div', 'ex-modes');
        var bList = el('button', 'stepper-btn' + (asTree ? '' : ' active'), t('as calls'));
        var bTree = el('button', 'stepper-btn' + (asTree ? ' active' : ''), t('as proof tree'));
        bList.type = bTree.type = 'button';
        modes.appendChild(bList); modes.appendChild(bTree);
        ui.body.appendChild(modes);
        var view = el('div', 'dv-view');
        ui.body.appendChild(view);
        function paint() {
          view.innerHTML = '';
          if (asTree) {
            var scroller = el('div', 'dv-scroll');
            scroller.appendChild(deriveTree(j.derivation));
            view.appendChild(scroller);
          } else {
            var ul = el('ul', 'trace dv-list');
            ul.appendChild(deriveList(j.derivation, 0));
            view.appendChild(ul);
          }
          bList.classList.toggle('active', !asTree);
          bTree.classList.toggle('active', asTree);
        }
        bList.addEventListener('click', function () { asTree = false; paint(); });
        bTree.addEventListener('click', function () { asTree = true; paint(); });
        paint();
        var verdict = el('div', 'ex-verdict' + (j.derivation.ok ? ' ok' : ' bad'));
        verdict.textContent = j.derivation.ok
          ? t('Infer returns') + ' ' + j.derivation.result
          : t('Infer fails') + ' ' + j.derivation.result;
        ui.body.appendChild(verdict);
      }).catch(function (e) { ui.busy(false); failLoad(ui, e); });
    }
    ui.form.addEventListener('submit', function (e) { e.preventDefault(); run(); });
    run();
  }

  // ----- reduce -----

  var KIND_LABEL = { beta: 'β', delta: 'δ', iota: 'ι', major: 'whnf', limit: '…' };
  var KIND_TEXT = { beta: t('beta: apply the function at the head'), delta: t('delta: unfold the definition at the head'), iota: t('iota: the recursor sees a constructor'), major: t('the major premise is computed first'), limit: t('step limit') };

  function setupReduce(box) {
    var prelude = childText(box, 'prelude');
    var ui = frame(box, t('reduction'), [
      { name: 'term', label: t('term'), value: attr(box, 'term', ''), wide: true },
      { name: 'ctx', label: t('context'), value: attr(box, 'ctx', '') }
    ]);
    function run() {
      ui.busy(true);
      request('reduce', [ui.fields.term.value, ui.fields.ctx.value], prelude).then(function (j) {
        ui.busy(false);
        if (j.error) { ui.error(j.error); return; }
        ui.error('');
        ui.body.innerHTML = '';
        var list = el('ol', 'rd-steps');
        if (!j.steps.length) list.appendChild(el('li', 'rd-none', t('no head reduction applies')));
        j.steps.forEach(function (s, i) {
          var li = el('li', 'rd-step rd-' + s.kind);
          var head = el('div', 'rd-head');
          head.appendChild(el('span', 'rd-kind', KIND_LABEL[s.kind] || s.kind));
          head.appendChild(el('span', 'rd-what', s.note || KIND_TEXT[s.kind] || ''));
          li.appendChild(head);
          if (s.before) li.appendChild(renderTokens(el('div', 'rd-before'), s.before));
          if (s.after) {
            var arrow = el('div', 'rd-arrow', '↓');
            li.appendChild(arrow);
            if (i === j.steps.length - 1) li.appendChild(renderTokens(el('div', 'rd-after'), s.after));
          }
          list.appendChild(li);
        });
        ui.body.appendChild(list);
        var res = el('div', 'rd-result');
        var w = el('div', 'rd-line');
        w.appendChild(el('span', 'rd-label', t('weak head normal form')));
        w.appendChild(renderTokens(el('span', ''), j.whnf));
        res.appendChild(w);
        if (j.stuck) res.appendChild(el('div', 'rd-stuck', j.stuck));
        if (!j.whnfIsNormal) {
          var n = el('div', 'rd-line');
          n.appendChild(el('span', 'rd-label', t('normal form (Normalize continues inside)')));
          n.appendChild(renderTokens(el('span', ''), j.normal));
          res.appendChild(n);
        } else {
          res.appendChild(el('div', 'rd-line rd-dim', t('this is also the normal form')));
        }
        ui.body.appendChild(res);
      }).catch(function (e) { ui.busy(false); failLoad(ui, e); });
    }
    ui.form.addEventListener('submit', function (e) { e.preventDefault(); run(); });
    run();
  }

  // ----- scope -----

  function setupScope(box) {
    var ui = frame(box, t('binders and scope'), [{ name: 'term', label: t('term'), value: attr(box, 'term', ''), wide: true }]);
    function run() {
      ui.busy(true);
      request('scope', [ui.fields.term.value]).then(function (j) {
        ui.busy(false);
        if (j.error) { ui.error(j.error); return; }
        ui.error('');
        ui.body.innerHTML = '';
        ui.body.appendChild(renderTokens(el('div', 'ex-term big'), j.tokens));
        var legend = el('div', 'sc-legend');
        legend.appendChild(el('span', 'sc-key tk tk-bound tk-b0', t('bound')));
        legend.appendChild(el('span', '', t('same colour as its binder; hover to see the pair')));
        legend.appendChild(el('span', 'sc-key tk tk-free', t('free')));
        legend.appendChild(el('span', '', j.free.length ? t('free variables') + ': ' + j.free.join(', ') : t('no free variables: the term is closed')));
        ui.body.appendChild(legend);
      }).catch(function (e) { ui.busy(false); failLoad(ui, e); });
    }
    ui.form.addEventListener('submit', function (e) { e.preventDefault(); run(); });
    run();
  }

  // ----- subst -----

  function setupSubst(box) {
    var ui = frame(box, t('substitution'), [
      { name: 'term', label: t('term'), value: attr(box, 'term', ''), wide: true },
      { name: 'var', label: t('replace'), value: attr(box, 'var', 'x') },
      { name: 'with', label: t('with'), value: attr(box, 'with', '') }
    ]);
    function run() {
      ui.busy(true);
      request('subst', [ui.fields.term.value, ui.fields['var'].value, ui.fields['with'].value]).then(function (j) {
        ui.busy(false);
        if (j.error) { ui.error(j.error); return; }
        ui.error('');
        ui.body.innerHTML = '';
        var top = el('div', 'sb-top');
        top.appendChild(renderTokens(el('span', 'ex-term'), j.term));
        var brack = el('span', 'sb-brackets');
        brack.appendChild(el('span', '', '[' + ui.fields['var'].value + ' ↦ '));
        brack.appendChild(renderTokens(el('span', ''), j.replacement));
        brack.appendChild(el('span', '', ']'));
        top.appendChild(brack);
        ui.body.appendChild(top);
        var cols = el('div', 'sb-cols');
        var a = el('div', 'sb-col' + (j.captured ? ' bad' : ''));
        a.appendChild(el('div', 'sb-h', t('naive substitution')));
        a.appendChild(renderTokens(el('div', 'ex-term'), j.naive));
        a.appendChild(el('div', 'sb-note', j.captured ? t('a free variable of the replacement has been captured: the meaning changed') : t('no capture here')));
        var b = el('div', 'sb-col ok');
        b.appendChild(el('div', 'sb-h', t('capture-avoiding substitution')));
        b.appendChild(renderTokens(el('div', 'ex-term'), j.safe));
        b.appendChild(el('div', 'sb-note', j.captured ? t('the binder was renamed first; the free variable stays free') : t('identical to the naive result')));
        cols.appendChild(a); cols.appendChild(b);
        ui.body.appendChild(cols);
        ui.body.appendChild(el('div', 'ex-verdict' + (j.captured ? ' bad' : ''), j.note));
      }).catch(function (e) { ui.busy(false); failLoad(ui, e); });
    }
    ui.form.addEventListener('submit', function (e) { e.preventDefault(); run(); });
    run();
  }

  // ----- proof explorer -----

  function goalsView(goals, current) {
    var wrap = el('div', 'goals');
    if (!goals.length) { wrap.appendChild(el('div', 'goal-none', t('no goals'))); return wrap; }
    goals.forEach(function (g) {
      var box = el('div', 'goal' + (g.id === current ? ' current' : ''));
      box.appendChild(el('div', 'goal-id', '?' + g.id));
      g.hyps.forEach(function (h) { box.appendChild(el('div', 'goal-hyp', h.name + ' : ' + h.type)); });
      box.appendChild(el('div', 'goal-target', g.target));
      wrap.appendChild(box);
    });
    return wrap;
  }

  function setupProof(box) {
    var script = childText(box, 'script');
    box.innerHTML = '';
    var bar = el('div', 'ex-bar');
    bar.appendChild(el('span', 'ex-title', attr(box, 'title', t('proof explorer'))));
    var status = el('span', 'ex-status', '');
    bar.appendChild(status);
    var edit = el('button', 'stepper-btn', t('edit script'));
    edit.type = 'button';
    bar.appendChild(edit);
    box.appendChild(bar);

    var editor = el('div', 'pf-editor');
    editor.hidden = true;
    var ta = el('textarea', 'pf-textarea');
    ta.value = script;
    ta.spellcheck = false;
    ta.rows = Math.max(4, script.split('\n').length + 1);
    var apply = el('button', 'playground-run', t('apply'));
    apply.type = 'button';
    editor.appendChild(ta);
    editor.appendChild(apply);
    box.appendChild(editor);

    var panels = el('div', 'pf-panels');
    var pScript = el('div', 'pf-panel pf-script');
    var pGoals = el('div', 'pf-panel pf-goals');
    var pTerm = el('div', 'pf-panel pf-term');
    panels.appendChild(pScript); panels.appendChild(pGoals); panels.appendChild(pTerm);
    box.appendChild(panels);
    var nav = el('div', 'stepper-bar pf-nav');
    var prev = el('button', 'stepper-btn', t('prev')); prev.type = 'button';
    var count = el('span', 'stepper-count', '');
    var next = el('button', 'stepper-btn', t('next')); next.type = 'button';
    var note = el('span', 'pf-note', '');
    nav.appendChild(prev); nav.appendChild(count); nav.appendChild(next); nav.appendChild(note);
    box.appendChild(nav);
    var err = el('div', 'ex-error'); err.hidden = true; box.appendChild(err);

    var steps = [];
    var index = 0;

    function paint() {
      var s = steps[index];
      pScript.innerHTML = '';
      pScript.appendChild(el('div', 'pf-h', t('script')));
      steps.forEach(function (st, i) {
        var line = el('div', 'pf-line' + (i === index ? ' on' : '') + (i < index ? ' done' : '') + (st.error ? ' bad' : ''));
        line.innerHTML = window.MiniLean.highlight ? window.MiniLean.highlight(st.command) : '';
        if (!window.MiniLean.highlight) line.textContent = st.command;
        line.addEventListener('click', function () { index = i; paint(); });
        pScript.appendChild(line);
      });
      pGoals.innerHTML = '';
      pGoals.appendChild(el('div', 'pf-h', s.kind === 'qed' ? t('kernel verdict') : t('goals after this command')));
      if (s.error) {
        pGoals.appendChild(el('div', 'pf-error', s.error));
      } else if (s.kind === 'qed') {
        pGoals.appendChild(el('div', 'pf-qed', t('QED. The kernel checked the complete term against the goal.')));
      } else if (s.kind === 'setup') {
        pGoals.appendChild(el('div', 'goal-none', t('declaration added to the signature; no proof in progress')));
      } else {
        pGoals.appendChild(goalsView(s.goals, s.current));
      }
      pTerm.innerHTML = '';
      pTerm.appendChild(el('div', 'pf-h', s.kind === 'qed' ? t('final proof term') : t('partial proof term')));
      if (s.kind === 'qed' && s.checked) {
        pTerm.appendChild(el('div', 'ex-term pf-checked', s.checked));
      } else if (s.term && s.term.length) {
        pTerm.appendChild(renderTokens(el('div', 'ex-term'), s.term, { currentHole: s.current }));
        var holes = s.goals.length;
        pTerm.appendChild(el('div', 'pf-sub', holes === 0 ? t('no holes remain') : holes + ' ' + (holes === 1 ? t('hole, the highlighted one is the current goal') : t('holes; the highlighted one is the current goal'))));
      } else {
        pTerm.appendChild(el('div', 'goal-none', t('no term yet')));
      }
      count.textContent = t('step') + ' ' + (index + 1) + ' / ' + steps.length;
      prev.disabled = index === 0;
      next.disabled = index === steps.length - 1;
      note.textContent = s.kind === 'tactic' ? t('line') + ' ' + s.line : '';
    }

    function run() {
      status.textContent = t('thinking...');
      request('trace', [], ta.value).then(function (j) {
        status.textContent = '';
        if (j.error) { err.hidden = false; err.textContent = j.error; return; }
        err.hidden = true;
        steps = j.steps;
        if (!steps.length) { err.hidden = false; err.textContent = t('the script is empty'); return; }
        index = Math.min(index, steps.length - 1);
        paint();
      }).catch(function (e) { status.textContent = ''; err.hidden = false; err.textContent = t('The in-browser kernel could not be loaded') + ' (' + e.message + ').'; });
    }
    prev.addEventListener('click', function () { if (index > 0) { index--; paint(); } });
    next.addEventListener('click', function () { if (index < steps.length - 1) { index++; paint(); } });
    box.tabIndex = 0;
    box.addEventListener('keydown', function (e) {
      if (e.target === ta) return;
      if (e.key === 'ArrowRight') { next.click(); e.preventDefault(); }
      if (e.key === 'ArrowLeft') { prev.click(); e.preventDefault(); }
    });
    edit.addEventListener('click', function () { editor.hidden = !editor.hidden; edit.textContent = editor.hidden ? t('edit script') : t('hide editor'); });
    apply.addEventListener('click', function () { index = 0; run(); });
    ta.addEventListener('keydown', function (e) { if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); index = 0; run(); } });
    run();
  }

  // ----- ctree -----

  function ctreeNode(n) {
    var node = el('div', 'ct-node');
    if (n.leaf) { node.appendChild(el('div', 'ct-leaf', n.leaf)); return node; }
    var head = el('div', 'ct-head');
    head.appendChild(el('span', 'ct-ctor', n.ctor));
    n.params.forEach(function (p) { head.appendChild(el('span', 'ct-param', p)); });
    n.fields.forEach(function (f) {
      if (!f.recursive) head.appendChild(el('span', 'ct-field', f.name + ' = ' + f.value));
    });
    node.appendChild(head);
    var rec = n.fields.filter(function (f) { return f.recursive; });
    if (rec.length) {
      var kids = el('div', 'ct-children');
      rec.forEach(function (f) {
        var slot = el('div', 'ct-slot');
        slot.appendChild(el('div', 'ct-slot-label', f.name + ' ' + t('(recursive field)')));
        slot.appendChild(ctreeNode(f.child));
        kids.appendChild(slot);
      });
      node.appendChild(kids);
    }
    var c = el('div', 'ct-case', t('recursor case') + ': ' + n.case);
    node.appendChild(c);
    return node;
  }

  function setupCtree(box) {
    var prelude = childText(box, 'prelude');
    var ui = frame(box, t('constructor tree'), [{ name: 'term', label: t('value'), value: attr(box, 'term', ''), wide: true }]);
    function run() {
      ui.busy(true);
      request('ctree', [ui.fields.term.value], prelude).then(function (j) {
        ui.busy(false);
        if (j.error) { ui.error(j.error); return; }
        ui.error('');
        ui.body.innerHTML = '';
        ui.body.appendChild(renderTokens(el('div', 'ex-term'), j.tokens));
        var tree = el('div', 'ct-tree');
        tree.appendChild(ctreeNode(j.tree));
        ui.body.appendChild(tree);
        ui.body.appendChild(el('div', 'ex-hint', t('R stands for the recursor applied to the same motive and cases; each (R field) is the induction hypothesis for that child.')));
      }).catch(function (e) { ui.busy(false); failLoad(ui, e); });
    }
    ui.form.addEventListener('submit', function (e) { e.preventDefault(); run(); });
    run();
  }

  // ----- universes (pure JS) -----

  function setupUniverses(box) {
    box.innerHTML = '';
    var bar = el('div', 'ex-bar');
    bar.appendChild(el('span', 'ex-title', t('the imax rule')));
    box.appendChild(bar);
    var body = el('div', 'ex-body un-body');
    box.appendChild(body);
    var controls = el('div', 'un-controls');
    function sel(labelText, init) {
      var label = el('label', 'ex-field');
      label.appendChild(el('span', 'ex-label', labelText));
      var s = el('select', 'ex-input');
      for (var i = 0; i <= 4; i++) { var o = el('option', '', 'Sort ' + i); o.value = String(i); s.appendChild(o); }
      s.value = String(init);
      label.appendChild(s);
      controls.appendChild(label);
      return s;
    }
    var su = sel(t('A lives in'), 1);
    var sv = sel(t('B lives in'), 0);
    body.appendChild(controls);
    var ladder = el('div', 'un-ladder');
    body.appendChild(ladder);
    var verdict = el('div', 'un-verdict');
    body.appendChild(verdict);
    function paint() {
      var u = +su.value, v = +sv.value;
      var r = v === 0 ? 0 : Math.max(u, v);
      ladder.innerHTML = '';
      for (var i = 4; i >= 0; i--) {
        var rung = el('div', 'un-rung' + (i === r ? ' result' : '') + (i === u ? ' u' : '') + (i === v ? ' v' : ''));
        rung.appendChild(el('span', 'un-name', 'Sort ' + i + (i === 0 ? '  ' + t('(propositions)') : '')));
        var tags = el('span', 'un-tags');
        if (i === u) tags.appendChild(el('span', 'un-tag', 'A'));
        if (i === v) tags.appendChild(el('span', 'un-tag', 'B'));
        if (i === r) tags.appendChild(el('span', 'un-tag hot', 'Π(x : A). B'));
        rung.appendChild(tags);
        ladder.appendChild(rung);
      }
      var why = v === 0
        ? t('imax_prop').replace('{u}', u)
        : t('imax_pred').replace(/\{u\}/g, u).replace(/\{v\}/g, v).replace('{r}', r);
      verdict.textContent = why;
    }
    su.addEventListener('change', paint);
    sv.addEventListener('change', paint);
    paint();
  }

  // ----- init -----

  var SETUP = { ast: setupAst, derive: setupDerive, reduce: setupReduce, scope: setupScope, subst: setupSubst, proof: setupProof, ctree: setupCtree, universes: setupUniverses };

  function init() {
    var boxes = document.querySelectorAll('div.explorer');
    for (var i = 0; i < boxes.length; i++) {
      var kind = boxes[i].getAttribute('data-kind');
      if (SETUP[kind]) {
        try { SETUP[kind](boxes[i]); } catch (e) { boxes[i].textContent = 'explorer failed: ' + e.message; }
      }
    }
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
