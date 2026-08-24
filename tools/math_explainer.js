(function () {
  'use strict';

  if (window.__cairnMathExplainerInstalled) return;
  window.__cairnMathExplainerInstalled = true;

  var ATOM_SELECTOR = '.mord,.mbin,.mrel,.mop,.mpunct,.mopen,.mclose';
  var panel;
  var lastFormula;

  function clean(value) {
    return String(value || '').replace(/\s+/g, ' ').trim();
  }

  function texOf(math) {
    var annotation = math && math.querySelector(
      'annotation[encoding="application/x-tex"]');
    return annotation ? annotation.textContent : '';
  }

  function nearbyText(math) {
    var host = math.closest(
      'p,li,.thm-stmt,.claim-stmt,.abstract,.panel,.body,.routebody');
    if (!host) host = math.parentElement;
    var value = clean(host && host.textContent);
    if (!value) return '';
    if (value.length > 260) value = value.slice(0, 257).replace(/\s+\S*$/, '') + '…';
    return value;
  }

  function escapePattern(value) {
    return String(value || '').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  }

  function nearbyDefinition(token, context) {
    if (!token || !context || token.length > 3) return '';
    var escaped = escapePattern(token);
    var patterns = [
      new RegExp('(?:let|write|put|set|denote(?: by)?)\\s+' + escaped +
        '\\s+(?:be|for|:=|=)\\s+([^.;:]{3,150})', 'i'),
      new RegExp(escaped + '\\s+(?:is|denotes|means)\\s+([^.;:]{3,150})', 'i')
    ];
    for (var i = 0; i < patterns.length; i++) {
      var match = context.match(patterns[i]);
      if (match) return clean(match[1]);
    }
    return '';
  }

  function localRole(token, tex, context, info) {
    var t = clean(token).replace(/\u200b/g, '');
    var s = tex || '';
    var definition = nearbyDefinition(t, context);
    if (definition) {
      return 'Here, “' + t + '” is the name introduced for ' + definition + '.';
    }

    if (t === 'H' && /H\s*=\s*\\(?:operatorname\s*\{)?(?:EL|E)/.test(s)) {
      return 'Here, H is the group constructed from elementary matrices; it is the group whose MF behavior the statement determines.';
    }
    if (t === 'L' && /L\s*=\s*\\(?:operatorname\s*\{)?(?:EL|E)/.test(s)) {
      return 'Here, L is the elementary-matrix subgroup that is conjugated into a smaller copy of itself.';
    }
    if (t === 'Q' && /W_?\{?Q\}?|\\pi_?\{?Q\}?/.test(s)) {
      return 'Here, Q is the quotient that remains visible after the hidden group is attached.';
    }
    if (t === 'Q' && /\\mathcal\s*\{?Q\}?|Q_?\{?\\mathbf/.test(s)) {
      return 'Here, Q denotes the norm matrix corona that receives the representation.';
    }
    if (t === 'd' && /d\s*=/.test(s)) {
      return 'Here, d names the concrete defect element defined by the expression to the right of the equals sign.';
    }
    if (t === 'D' && /D\s*\(\s*[A-Z]/.test(s)) {
      return 'Here, D packages all commutators created by the displayed compression and centralizer data.';
    }
    if ((t === 'π' || t === 'ρ' || t === 'Θ' || t === 'V') &&
        /(?:\\to|\\longrightarrow|→)/.test(s)) {
      return 'Here, “' + t + '” names the map shown by the arrow; the expression before the arrow is its source and the expression after it is its target.';
    }
    if ((t === 'i' || t === 'j' || t === 'n') &&
        new RegExp('[_^]\\{?' + escapePattern(t) + '\\}?').test(s)) {
      return 'Here, “' + t + '” is an index: it selects the particular entry, term, or stage named by the symbol it is attached to.';
    }
    if (/^[A-Za-zΑ-Ωα-ω]$/.test(t) &&
        new RegExp(escapePattern(t) + '\\s*(?:=|:=)').test(s)) {
      return 'Here, “' + t + '” is being defined by the expression on the other side of the equals sign.';
    }
    if (/^[A-Za-zΑ-Ωα-ω]$/.test(t) &&
        new RegExp(escapePattern(t) + '\\s*(?:\\le|\\subset|≤|⊆)').test(s)) {
      return 'Here, “' + t + '” is the object being asserted to lie inside the object written to its right.';
    }
    if (/^[A-Za-zΑ-Ωα-ω]$/.test(t)) {
      return 'Here, “' + t + '” is the local name used in this formula. The whole-formula explanation and the quoted sentence below determine its role without assuming that the same letter means the same thing elsewhere.';
    }
    return 'Here, this symbol has its ordinary mathematical role—' + info.name + '—inside the complete statement explained below.';
  }

  function item(name, meaning) {
    return { name: name, meaning: meaning };
  }

  function sourceHas(tex, pattern) {
    return pattern.test(tex || '');
  }

  function explainToken(token, tex, atom) {
    var t = clean(token).replace(/\u200b/g, '');
    var rel = atom && atom.classList.contains('mrel');
    var bin = atom && atom.classList.contains('mbin');

    if (t === '=') return item('equals',
      'The expressions on the two sides name the same mathematical object or quantity.');
    if (t === '≠' || t === '=/=') return item('is not equal to',
      'The two sides are different.');
    if (t === '∈') return item('belongs to',
      'The object on the left is one of the elements collected by the object on the right.');
    if (t === '∉') return item('does not belong to',
      'The object on the left is not an element of the object on the right.');
    if (t === '≤' || t === '⊆') return item('is contained in',
      'Everything in the object on the left also lies in the object on the right. For groups, this means “is a subgroup of.”');
    if (t === '⊴' || t === '◁') return item('is a normal subgroup of',
      'The subgroup on the left is preserved when elements of the larger group conjugate it.');
    if (t === '→' || t === '⟶') return item('maps to',
      'This arrow introduces a structure-preserving function from the object on the left to the object on the right.');
    if (t === '↪') return item('embeds into',
      'This is an injective map: distinct inputs remain distinct in the target.');
    if (t === '↠') return item('maps onto',
      'This is a surjective map: every element of the target is reached.');
    if (t === '⇒' || t === '⟹') return item('implies',
      'Whenever the statement on the left is true, the statement on the right must also be true.');
    if (t === '⇔' || t === '↔') return item('if and only if',
      'Each statement implies the other, so the two conditions are equivalent.');
    if (t === '≅' || t === '≃') return item('is isomorphic to',
      'The two objects may be presented differently but have the same mathematical structure.');
    if (t === '×') return item('direct product',
      'An element consists of one choice from each factor, with operations performed coordinate by coordinate.');
    if (t === '⊕') return item('direct sum',
      'The object is assembled from independent pieces placed side by side.');
    if (t === '⊗') return item('tensor product',
      'This combines two linear objects so that bilinear interactions become ordinary linear ones.');
    if (t === '⋊' || t === '⋉') return item('semidirect product',
      'This builds a group from two groups while allowing one of them to act on the other.');
    if ((t === '*' || t === '∗') && sourceHas(tex, /\*\s*_\s*(?:\{|[A-Za-z])|\\ast\s*_/)) {
      return item('amalgamated free product',
        'Two groups are joined while identifying the subgroup written beneath the star. No other relations are added.');
    }
    if (t === '*' && sourceHas(tex, /\^\s*\*|\^\{\\ast\}/)) return item('adjoint',
      'For a matrix or operator, this means transpose and complex conjugate.');
    if (t === '∩') return item('intersection',
      'This keeps exactly the elements shared by both collections.');
    if (t === '∪') return item('union',
      'This collects the elements that appear in either collection.');
    if (t === '∑') return item('sum',
      'Add the indicated family of terms. The limits written above and below say which terms are included.');
    if (t === '∏') return item('product',
      'Multiply or assemble the indicated family of factors.');
    if (t === '∞') return item('infinity',
      'There is no finite upper bound in the direction being discussed.');
    if (t === '⊥') return item('orthogonal',
      'The two directions have zero inner product; geometrically, they meet at a right angle.');
    if (t === '‖' || t === '∥') return item('norm',
      'The double bars measure the size of a vector, matrix, operator, or error.');
    if (t === '[' || t === ']') {
      if (sourceHas(tex, /\[[^\]]*,[^\]]*\]/)) return item('commutator bracket',
        'The bracket measures failure to commute. For group elements, [a,b] is trivial exactly when a and b commute.');
      return item('bracket', 'Brackets group part of the expression so it is read as one unit.');
    }
    if (t === '⟨' || t === '⟩') {
      if (sourceHas(tex, /\\langle\s*[^,]+\\rangle/)) return item('generated subgroup',
        'The angle brackets mean the smallest subgroup containing the listed element or elements.');
      return item('angle bracket',
        'Depending on context, angle brackets denote a generated subgroup, an inner product, or a pairing.');
    }
    if (t === '(' || t === ')' || t === '{' || t === '}') return item('grouping mark',
      'These marks keep the enclosed expression together, just as parentheses do in ordinary arithmetic.');
    if (t === ',') return item('separator',
      'The comma separates inputs, elements, or conditions that are being listed together.');
    if (t === '1') return item('identity element',
      'For groups and matrices, 1 is the do-nothing element: multiplying by it changes nothing.');
    if (t === '0') return item('zero',
      'This is the additive identity: adding it changes nothing. For a map or projection it can also mean the trivial one.');

    if (/^Rad$/i.test(t)) return item('MF radical',
      'The MF radical is the set of group elements sent to the identity by every homomorphism into every norm matrix corona.');
    if (t === 'MF') return item('MF',
      'MF means “matricial field.” An MF group can be faithfully modeled by finite unitary matrices whose multiplication errors vanish in operator norm.');
    if (t === 'EL') return item('elementary linear group',
      'This group is generated by matrices that differ from the identity in one off-diagonal entry.');
    if (t === 'GL') return item('general linear group',
      'The group of all invertible matrices of the stated size over the stated coefficient system.');
    if (t === 'U') return item('unitary group',
      'The group of matrices or operators that preserve lengths and angles.');
    if (t === 'Hom') return item('homomorphisms',
      'Hom collects every structure-preserving map from the first object to the second.');
    if (t === 'ker') return item('kernel',
      'The kernel consists of exactly the elements that a map sends to the identity.');
    if (t === 'Fix') return item('fixed vectors',
      'These are the vectors left unchanged by every operator in the indicated group.');
    if (t === 'tr' || t === 'Tr') return item('trace',
      'The trace adds the diagonal entries of a matrix. Here it is used as a dimension-like measurement.');
    if (t === 'rank') return item('rank',
      'The rank is the dimension of the range: the number of independent output directions.');
    if (t === 'span') return item('linear span',
      'The smallest linear space containing the listed vectors or subspaces.');
    if (t === 'supp') return item('support',
      'The part of the space or function on which the object is nonzero.');
    if (t === 'Aut') return item('automorphisms',
      'All invertible structure-preserving maps from an object to itself.');
    if (t === 'End') return item('endomorphisms',
      'All structure-preserving maps from an object to itself, whether invertible or not.');
    if (t === 'Ad') return item('conjugation action',
      'Ad describes the operation x ↦ uxu⁻¹: change coordinates by u, apply x, then change back.');

    if (t === 'C' && sourceHas(tex, /\\mathbb\s*\{?C\}?|\\C\b/)) return item('the complex numbers',
      'Numbers with a real part and an imaginary part. Complex matrices are the finite models used here.');
    if (t === 'C' && sourceHas(tex, /C_\{?G|C_\{?[A-Z]\}?\s*\(/)) return item('centralizer',
      'The centralizer of a subgroup is the collection of elements that commute with every element of that subgroup.');
    if (t === 'F' && sourceHas(tex, /\\F\s*_?\s*\{?2\}?|\\mathbb\s*\{F\}/)) return item('the field with two elements',
      'This number system contains only 0 and 1, with 1 + 1 = 0.');
    if (t === 'Q' && sourceHas(tex, /\\mathcal\s*\{?Q\}?|Q_\{?\\mathbf/)) return item('a norm matrix corona',
      'A norm matrix corona records infinite sequences of finite matrices while treating any sequence converging to zero as negligible.');
    if (t === 'L' && sourceHas(tex, /L_\{?\\F|L_\{?\\mathbb/)) return item('the binary Leavitt algebra',
      'A coefficient algebra containing two algebraic copies of itself. It supplies the self-compression used in the construction.');
    if (t === 'e' && sourceHas(tex, /e_\{?[ij0-9]/)) return item('an elementary matrix',
      'This is the identity matrix with one additional off-diagonal entry, specified by the lower indices.');
    if ((t === 's' || t === 't') && sourceHas(tex, /s_[01]|t_[01]/)) return item('a Leavitt generator',
      'One of four coefficient-algebra elements whose relations split one algebraic module into two copies of itself.');
    if (t === 'q' && sourceHas(tex, /q\s*=\s*s_?\{?1\}?\s*t_?\{?1\}?/)) return item('the complementary Leavitt idempotent',
      'This element behaves like a projection onto the second algebraic copy created by the Leavitt relations.');

    var named = {
      G: ['the ambient group', 'The group currently being studied. A group is a collection of reversible operations with an associative multiplication and an identity.'],
      H: ['the main group', 'The particular group to which the main theorem is applied. In this paper it is the elementary group built from the binary Leavitt algebra.'],
      L: ['the compressed subgroup', 'A subgroup with property (T) that a group element conjugates into a copy lying inside itself.'],
      K: ['a normal Kazhdan subgroup', 'A property-(T) subgroup preserved by conjugation from the whole ambient group.'],
      B: ['the hidden seed group', 'A group whose every map into an MF group is trivial; it supplies the invisible part of the construction.'],
      Q: ['the visible quotient group', 'The group that remains visible to MF targets after the hidden part is attached.'],
      W: ['the constructed group', 'The group obtained by attaching the hidden seed to the prescribed visible quotient.'],
      M: ['an MF target group', 'A group that admits faithful finite-matrix models in operator norm.'],
      T: ['a target group', 'The group receiving a homomorphism; its stated property determines what the source map can remember.'],
      A: ['the shared cyclic subgroup', 'The subgroup identified in both pieces of the amalgamated product.'],
      R: ['the coefficient ring', 'The arithmetic system whose elements appear as matrix entries.'],
      D: ['the compression defect', 'The normal subgroup generated by commutators that measure what one-sided compression changes.'],
      d: ['the defect element', 'A concrete nonidentity element forced to become the identity in every MF target.'],
      c: ['a centralizing element', 'An element that commutes with every element of the subgroup L.'],
      u: ['the compressing element', 'Conjugation by this element sends the subgroup L into a copy contained in L.'],
      τ: ['the compression matrix', 'The explicit invertible matrix whose conjugation places the Kazhdan subgroup inside itself.'],
      ℓ: ['an element of L', 'A generic member of the compressed subgroup.'],
      π: ['a homomorphism', 'A structure-preserving map between groups. When written π with a subscript Q here, it is the quotient map onto Q.'],
      ρ: ['a representation', 'A homomorphism that realizes abstract group elements as concrete matrices or operators.'],
      Θ: ['a corona representation', 'A homomorphism from the group into the unitary group of a norm matrix corona.'],
      V: ['a finite-matrix model', 'A sequence of unitary matrices intended to approximate the group multiplication law.'],
      p: ['a projection', 'An operator satisfying p² = p; it selects a subspace.'],
      q: ['a complementary projection or quotient label', 'Its exact role is fixed by the nearby sentence; in projection formulas it selects the complementary invariant sector.'],
      n: ['an index', 'Usually the stage of a matrix sequence or a matrix dimension.'],
      i: ['an index', 'A label selecting a row, column, generator, or term.'],
      j: ['an index', 'A second label selecting a row, column, generator, or term.'],
      x: ['an element', 'A generic element of the group, ring, or space named nearby.'],
      g: ['a group element', 'A generic reversible operation in the group.'],
      h: ['a subgroup element', 'A generic element of the subgroup under discussion.']
    };
    if (named[t]) return item(named[t][0], named[t][1]);

    if (/^\d+$/.test(t)) return item('a number or index',
      'This number specifies a size, stage, exponent, or count. The nearby sentence determines which.');
    if (/^[A-Za-zΑ-Ωα-ω]$/.test(t)) return item('a locally named object',
      'This letter is a label introduced by the nearby sentence or theorem. Read the context shown below to see its exact role here.');
    if (rel) return item('a relation',
      'This symbol states how the expression on its left is related to the expression on its right.');
    if (bin) return item('an operation',
      'This symbol combines the objects immediately to its left and right.');
    return item('part of the notation',
      'This mark helps name or organize an object in the formula. Its precise local role is given by the surrounding sentence.');
  }

  function explainFormula(tex) {
    var s = tex || '';
    if (/\\Rad_/.test(s) && /=/.test(s)) return 'This says the MF radical is exactly the group written on the other side. In plain language, every MF-target representation erases every element of that group.';
    if (/\\operatorname\s*\{Hom\}|\\Hom\b/.test(s)) return 'This compares complete collections of structure-preserving maps. The assertion says that a map from one group contains exactly the same target-visible information as a map from the other.';
    if (/\\ker\b/.test(s)) return 'This identifies exactly which elements are erased by the displayed map.';
    if (/u\s*L\s*u\^\{-?1\}|uLu/.test(s)) return 'Conjugating the subgroup L by u produces a copy that lies inside L. This one-sided self-compression is the starting point of the argument.';
    if (/\\trianglelefteq|\\triangleleft/.test(s)) return 'This states that one group is a normal subgroup of another, so conjugation by the larger group preserves it.';
    if (/\[[^\]]*,[^\]]*\]/.test(s)) return 'The displayed bracket is a commutator. It records whether two operations commute; a value of 1 means that their order does not matter.';
    if (/\\cong|\\simeq|\\equiv/.test(s)) return 'This says the two displayed objects carry the same mathematical structure, even if their descriptions look different.';
    if (/\\hookrightarrow/.test(s)) return 'This states that the object on the left embeds faithfully into the object on the right.';
    if (/\\twoheadrightarrow/.test(s)) return 'This states that the map reaches every element of the object on the right.';
    if (/\\to|\\longrightarrow|\\mapsto/.test(s)) return 'This formula describes a map and, when an arrow with an input is shown, what the map does to that input.';
    if (/\\le|\\subset/.test(s)) return 'This is a containment statement: every object represented on the left also belongs to the object on the right.';
    if (/=/.test(s)) return 'This equality says that the constructions on the two sides produce the same mathematical object.';
    return 'This formula records a precise relationship among the objects named in the nearby sentence. Click another symbol to unpack it one piece at a time.';
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
      '<div class="math-explainer-head">' +
        '<span>Plain-language math</span>' +
        '<button type="button" class="math-explainer-close" aria-label="Close explanation">×</button>' +
      '</div>' +
      '<div class="math-explainer-symbol" aria-hidden="true"></div>' +
      '<h2 id="math-explainer-title"></h2>' +
      '<p class="math-explainer-meaning"></p>' +
      '<div class="math-explainer-section">What it means here</div>' +
      '<p class="math-explainer-local"></p>' +
      '<div class="math-explainer-section">How to read the formula</div>' +
      '<p class="math-explainer-formula"></p>' +
      '<div class="math-explainer-context-wrap">' +
        '<div class="math-explainer-section">In this sentence</div>' +
        '<p class="math-explainer-context"></p>' +
      '</div>';
    document.body.appendChild(panel);
    panel.querySelector('.math-explainer-close').addEventListener('click', closePanel);
    return panel;
  }

  function openExplanation(atom, math) {
    var token = clean(atom && atom.textContent) || 'formula';
    var tex = texOf(math);
    var info = explainToken(token, tex, atom);
    var context = nearbyText(math);
    var box = ensurePanel();
    box.querySelector('.math-explainer-symbol').textContent = token;
    box.querySelector('#math-explainer-title').textContent = info.name;
    box.querySelector('.math-explainer-meaning').textContent = info.meaning;
    box.querySelector('.math-explainer-local').textContent =
      localRole(token, tex, context, info);
    box.querySelector('.math-explainer-formula').textContent = explainFormula(tex);
    var wrap = box.querySelector('.math-explainer-context-wrap');
    wrap.hidden = !context;
    box.querySelector('.math-explainer-context').textContent = context;
    box.hidden = false;
    lastFormula = math;
  }

  function closePanel() {
    if (!panel) return;
    panel.hidden = true;
    if (lastFormula && lastFormula.focus) lastFormula.focus({ preventScroll: true });
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
      math.setAttribute('tabindex', '0');
      math.setAttribute('title', 'Click any symbol for a plain-language explanation');
      math.setAttribute('data-math-help', 'true');
      var atoms = visual.querySelectorAll(ATOM_SELECTOR);
      for (var j = 0; j < atoms.length; j++) {
        var atom = atoms[j];
        if (!clean(atom.textContent)) continue;
        if (atom.querySelector(ATOM_SELECTOR)) continue;
        atom.classList.add('math-symbol-help');
      }
    }
  }

  function addPrompt() {
    if (document.querySelector('.math-help-prompt')) return;
    var anchor = document.querySelector('.paper-key, .paper-head, nav.top, header');
    if (!anchor || !document.querySelector('.katex')) return;
    var prompt = document.createElement('button');
    prompt.type = 'button';
    prompt.className = 'math-help-prompt';
    prompt.textContent = 'Math is interactive — click any symbol for plain English.';
    prompt.addEventListener('click', function () {
      var math = document.querySelector('.katex.math-help-ready');
      var atom = math && math.querySelector('.math-symbol-help');
      if (math && atom) openExplanation(atom, math);
    });
    if (anchor.classList.contains('paper-key')) anchor.insertAdjacentElement('afterend', prompt);
    else anchor.insertAdjacentElement('afterend', prompt);
  }

  document.addEventListener('click', function (event) {
    if (event.target.closest && event.target.closest('.math-explainer')) return;
    var atom = event.target.closest && event.target.closest('.math-symbol-help');
    var math = atom && atom.closest('.katex');
    if (atom && math) {
      event.preventDefault();
      event.stopPropagation();
      openExplanation(atom, math);
      return;
    }
    if (panel && !panel.hidden && !event.target.closest('.math-help-prompt')) closePanel();
  }, true);

  document.addEventListener('keydown', function (event) {
    if (event.key === 'Escape' && panel && !panel.hidden) {
      event.preventDefault();
      closePanel();
      return;
    }
    if ((event.key === 'Enter' || event.key === ' ') &&
        event.target.classList && event.target.classList.contains('math-help-ready')) {
      var atom = event.target.querySelector('.math-symbol-help');
      if (atom) {
        event.preventDefault();
        openExplanation(atom, event.target);
      }
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
          if (node.matches && node.matches('.katex')) decorate(node.parentElement || node);
          else decorate(node);
        }
      }
      addPrompt();
    });
    observer.observe(document.body, { childList: true, subtree: true });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();

  window.__cairnMathExplainer = {
    explainToken: function (token, tex) { return explainToken(token, tex, null); },
    explainFormula: explainFormula,
    localRole: function (token, tex, context) {
      return localRole(token, tex, context, explainToken(token, tex, null));
    },
    decorate: decorate
  };
}());
