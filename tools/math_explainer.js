(function () {
  'use strict';

  if (window.__cairnMathExplainerInstalled) return;
  window.__cairnMathExplainerInstalled = true;

  var panel;
  var lastObject;
  var history = [];
  var current;

  /* Words inside an explanation may be followed to these short definitions.
     Mathematical expressions themselves are never inferred from this table;
     every clickable expression is declared explicitly in the TeX source. */
  var TERMS = {
    'group': entry('group',
      'A collection of reversible operations. The operations can be combined, there is a do-nothing operation, and every operation can be undone.'),
    'subgroup': entry('subgroup',
      'A collection of operations inside a group that is itself a group.'),
    'normal subgroup': entry('normal subgroup',
      'A subgroup unchanged by conjugation from the whole group. Declaring all of its elements to be the identity produces a quotient group.'),
    'MF group': entry('MF group',
      'A group that embeds faithfully into finite unitary matrices in the limit, with multiplication errors tending to zero in operator norm.'),
    'homomorphism': entry('homomorphism',
      'A map that preserves multiplication and the identity. It translates one group into another without changing the group laws.'),
    'representation': entry('representation',
      'A homomorphism that realizes abstract group elements as concrete matrices or operators.'),
    'identity': entry('identity',
      'The do-nothing element. A representation erases an element when it sends that element to the identity.'),
    'kernel': entry('kernel',
      'All elements that a homomorphism sends to the identity.'),
    'quotient group': entry('quotient group',
      'The group left after every element of a chosen normal subgroup is declared to be the identity.'),
    'norm matrix corona': entry('norm matrix corona',
      'An object made from sequences of finite matrices. Two sequences are identified when their operator-norm difference tends to zero.'),
    'operator norm': entry('operator norm',
      'The largest amount by which a matrix stretches a vector. A small operator norm means the matrix is small in every direction.'),
    'unitary matrix': entry('unitary matrix',
      'A matrix that preserves lengths and angles. Its inverse is its conjugate transpose.'),
    'projection': entry('projection',
      'An operator that keeps one chosen subspace and sends all perpendicular directions to zero.'),
    'property (T)': entry('property (T)',
      'A rigidity property: sufficiently good almost-fixed vectors force the existence of a genuinely fixed vector.'),
    'MF radical': entry('MF radical',
      'All group elements erased by every homomorphism into every norm matrix corona.'),
    'Leavitt algebra': entry('Leavitt algebra',
      'An algebra with four elements s₀,s₁,t₀,t₁ that split one free module into two copies and recombine them. The identities t_i s_j = δ_ij and s₀t₀ + s₁t₁ = 1 make the splitting and recombination exact.'),
    'elementary matrix': entry('elementary matrix',
      'The identity matrix with one extra off-diagonal entry. These matrices generate the elementary linear group.'),
    'commutator': entry('commutator',
      'For a and b, the commutator is aba⁻¹b⁻¹. It equals the identity exactly when ab and ba are equal.')
  };

  function entry(name, explanation) {
    return { name: name, explanation: explanation };
  }

  function clean(value) {
    return String(value || '').replace(/\u200b/g, '').replace(/\s+/g, ' ').trim();
  }

  function compact(value) {
    return String(value || '').replace(/\s+/g, '');
  }

  function parseAttributes(source) {
    var attrs = {};
    var re = /([a-z][a-z-]*)="([^"]*)"/gi;
    var match;
    while ((match = re.exec(source))) attrs[match[1]] = match[2];
    return attrs;
  }

  function parseSourceExplanations(source) {
    var result = [];
    var re = /^\s*%<webmath\s+([^>]+)>\s*$([\s\S]*?)^\s*%<\/webmath>\s*$/gm;
    var match;
    var group = -1;
    var previousEnd = 0;
    while ((match = re.exec(String(source || '')))) {
      if (group < 0 || String(source || '').slice(previousEnd, match.index).trim()) group++;
      var attrs = parseAttributes(match[1]);
      var explanation = match[2].split('\n').map(function (line) {
        return line.replace(/^\s*%\s?/, '');
      }).join(' ').replace(/\s+/g, ' ').trim();
      if (!attrs.object || !attrs.when || !attrs.title || !explanation) continue;
      result.push({
        object: attrs.object,
        when: compact(attrs.when),
        group: group,
        name: attrs.title,
        explanation: explanation
      });
      previousEnd = re.lastIndex;
    }
    return result;
  }

  var SOURCE_EXPLANATIONS = parseSourceExplanations(window.PAPER_EXPLANATION_SOURCE);
  var SOURCE_GROUPS = [];
  var sourceGroupCursor = 0;
  SOURCE_EXPLANATIONS.forEach(function (item) {
    if (!SOURCE_GROUPS[item.group]) SOURCE_GROUPS[item.group] = [];
    SOURCE_GROUPS[item.group].push(item);
  });

  function sourceExplanation(text, tex, candidates) {
    var object = clean(text);
    var formula = compact(tex);
    var best = null;
    var pool = candidates || SOURCE_EXPLANATIONS;
    for (var i = 0; i < pool.length; i++) {
      var candidate = pool[i];
      if (candidate.object !== object || formula.indexOf(candidate.when) < 0) continue;
      if (!best || candidate.when.length > best.when.length) best = candidate;
    }
    return best ? entry(best.name, best.explanation) : null;
  }

  function texOf(math) {
    var annotation = math && math.querySelector('annotation[encoding="application/x-tex"]');
    return annotation ? annotation.textContent : '';
  }

  function explainTerm(term) {
    return TERMS[clean(term)] || null;
  }

  function setLinkedText(node, value, excludedTerm) {
    node.textContent = '';
    var text = String(value || '');
    var cursor = 0;
    var pattern = /\[\[([^|\]]+)(?:\|([^\]]+))?\]\]/g;
    var match;
    while ((match = pattern.exec(text))) {
      if (match.index > cursor) node.appendChild(document.createTextNode(text.slice(cursor, match.index)));
      var canonical = clean(match[1]);
      var label = clean(match[2] || match[1]);
      if (!TERMS[canonical] || canonical === excludedTerm) {
        node.appendChild(document.createTextNode(label));
      } else {
        var button = document.createElement('button');
        button.type = 'button';
        button.className = 'math-term-help';
        button.setAttribute('data-term', canonical);
        button.textContent = label;
        node.appendChild(button);
      }
      cursor = pattern.lastIndex;
    }
    if (cursor < text.length) node.appendChild(document.createTextNode(text.slice(cursor)));
  }

  function ensurePanel() {
    if (panel) return panel;
    panel = document.createElement('aside');
    panel.className = 'math-explainer';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-modal', 'false');
    panel.setAttribute('aria-labelledby', 'math-explainer-title');
    panel.innerHTML =
      '<button type="button" class="math-explainer-back" aria-label="Back to previous explanation">←</button>' +
      '<button type="button" class="math-explainer-close" aria-label="Close explanation">×</button>' +
      '<div class="math-explainer-symbol" aria-hidden="true"></div>' +
      '<h2 id="math-explainer-title"></h2>' +
      '<p class="math-explainer-meaning"></p>';
    document.body.appendChild(panel);
    panel.querySelector('.math-explainer-back').addEventListener('click', goBack);
    panel.querySelector('.math-explainer-close').addEventListener('click', closePanel);
    return panel;
  }

  function render(state) {
    var box = ensurePanel();
    current = state;
    box.querySelector('.math-explainer-symbol').textContent = state.symbol;
    box.querySelector('#math-explainer-title').textContent = state.info.name;
    setLinkedText(box.querySelector('.math-explainer-meaning'),
      state.info.explanation, state.term || '');
    box.querySelector('.math-explainer-back').hidden = history.length === 0;
    box.hidden = false;
  }

  function openTerm(term) {
    var canonical = clean(term);
    var info = explainTerm(canonical);
    if (!info) return;
    if (current) history.push(current);
    render({ symbol: canonical, info: info, term: canonical });
  }

  function goBack() {
    if (history.length) render(history.pop());
  }

  function closePanel() {
    if (!panel) return;
    panel.hidden = true;
    history = [];
    current = null;
    if (lastObject && lastObject.focus) lastObject.focus({ preventScroll: true });
  }

  function openObject(node, math) {
    var info = node.__mathExplanation;
    if (!info) return;
    history = [];
    render({ symbol: clean(node.textContent), info: info, term: '' });
    lastObject = node;
  }

  function isTopLevelMathObject(node) {
    if (!node.classList) return false;
    return node.classList.contains('mord') || node.classList.contains('mop') ||
      node.classList.contains('mbin') || node.classList.contains('mrel');
  }

  function decorate(root) {
    if (!root || !root.querySelectorAll) return;
    var formulas = root.querySelectorAll('.katex');
    for (var i = 0; i < formulas.length; i++) {
      var math = formulas[i];
      if (math.classList.contains('math-help-ready')) continue;
      var visual = math.querySelector('.katex-html');
      if (!visual) continue;
      math.classList.add('math-help-ready');
      var tex = texOf(math);
      var group = SOURCE_GROUPS[sourceGroupCursor] || [];
      var matchesGroup = group.some(function (candidate) {
        return compact(tex).indexOf(candidate.when) >= 0;
      });
      if (!matchesGroup) continue;
      sourceGroupCursor++;
      var bases = visual.querySelectorAll('.base');
      for (var j = 0; j < bases.length; j++) {
        var children = bases[j].children;
        for (var k = 0; k < children.length; k++) {
          var node = children[k];
          if (!isTopLevelMathObject(node)) continue;
          var info = sourceExplanation(clean(node.textContent), tex, group);
          if (!info) continue;
          node.__mathExplanation = info;
          node.classList.add('math-symbol-help');
          node.setAttribute('tabindex', '0');
          node.setAttribute('role', 'button');
          node.setAttribute('aria-label', 'Explain ' + info.name);
          node.setAttribute('title', info.name);
        }
      }
    }
  }

  function addPrompt() {
    if (document.querySelector('.math-help-prompt')) return;
    var anchor = document.querySelector('.paper-key, .paper-head, nav.top, header');
    if (!anchor || !document.querySelector('.math-symbol-help')) return;
    var prompt = document.createElement('p');
    prompt.className = 'math-help-prompt';
    prompt.textContent = 'Click highlighted math.';
    anchor.insertAdjacentElement('afterend', prompt);
  }

  document.addEventListener('click', function (event) {
    var term = event.target.closest && event.target.closest('.math-term-help');
    if (term) {
      event.preventDefault(); event.stopPropagation();
      openTerm(term.getAttribute('data-term')); return;
    }
    if (event.target.closest && event.target.closest('.math-explainer')) return;
    var object = event.target.closest && event.target.closest('.math-symbol-help');
    var math = object && object.closest('.katex');
    if (object && math) {
      event.preventDefault(); event.stopPropagation(); openObject(object, math); return;
    }
    if (panel && !panel.hidden && !event.target.closest('.math-help-prompt')) closePanel();
  }, true);

  document.addEventListener('keydown', function (event) {
    if (event.key === 'Escape' && panel && !panel.hidden) {
      event.preventDefault(); closePanel(); return;
    }
    if ((event.key === 'Enter' || event.key === ' ') &&
        event.target.classList && event.target.classList.contains('math-symbol-help')) {
      var math = event.target.closest('.katex');
      if (math) { event.preventDefault(); openObject(event.target, math); }
    }
  });

  function start() {
    decorate(document);
    addPrompt();
    var observer = new MutationObserver(function (records) {
      for (var i = 0; i < records.length; i++) {
        for (var j = 0; j < records[i].addedNodes.length; j++) {
          var node = records[i].addedNodes[j];
          if (node.nodeType !== 1) continue;
          decorate(node.matches && node.matches('.katex') ? node.parentElement || node : node);
        }
      }
      addPrompt();
    });
    observer.observe(document.body, { childList: true, subtree: true });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();

  window.__cairnMathExplainer = {
    parseSourceExplanations: parseSourceExplanations,
    sourceExplanation: sourceExplanation,
    explainTerm: explainTerm,
    decorate: decorate
  };
}());
