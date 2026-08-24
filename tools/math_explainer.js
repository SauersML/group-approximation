(function () {
  'use strict';

  if (window.__cairnMathExplainerInstalled) return;
  window.__cairnMathExplainerInstalled = true;

  var ATOM_SELECTOR = '.mord,.mbin,.mrel,.mop,.mpunct,.mopen,.mclose';
  var panel;
  var lastFormula;
  var explanationHistory = [];
  var currentExplanation;

  var TERM_INFO = {
    'group': item('group',
      'A collection of reversible operations that can be combined. There is an identity operation that does nothing, and every operation has an inverse that undoes it.'),
    'subgroup': item('subgroup',
      'A smaller collection inside a group that is itself a group under the same operation.'),
    'normal subgroup': item('normal subgroup',
      'A subgroup that the whole group preserves under conjugation. This is exactly the kind of subgroup that can be collapsed to form a quotient group.'),
    'MF group': item('MF group',
      'A group that can be represented faithfully by finite unitary matrices in the limit, with multiplication errors tending to zero in operator norm.'),
    'homomorphism': item('homomorphism',
      'A map between groups that preserves multiplication and the identity. It translates operations in one group into operations in another without changing their algebraic relationships.'),
    'representation': item('representation',
      'A homomorphism that turns abstract group elements into concrete matrices or operators.'),
    'identity': item('identity',
      'The do-nothing element of a group. Sending an element to the identity means the representation cannot distinguish that element from doing nothing.'),
    'kernel': item('kernel',
      'The elements that a homomorphism sends to the identity. The kernel measures exactly what information the map erases.'),
    'quotient group': item('quotient group',
      'A group formed by treating every element of a chosen normal subgroup as the identity. It keeps the structure that remains after those elements are collapsed.'),
    'quotient map': item('quotient map',
      'The natural homomorphism from a group to a quotient group. Its kernel is exactly the normal subgroup being collapsed.'),
    'norm matrix corona': item('norm matrix corona',
      'A single algebraic object built from an infinite sequence of finite matrix algebras. Two matrix sequences count as the same when their operator-norm difference tends to zero.'),
    'operator norm': item('operator norm',
      'The largest factor by which a matrix can stretch a vector. An error tending to zero in operator norm is small in every direction.'),
    'unitary matrix': item('unitary matrix',
      'A matrix that preserves lengths and angles. Its inverse is its conjugate transpose.'),
    'projection': item('projection',
      'A linear operation that keeps one subspace and sends the complementary directions to zero.'),
    'trace': item('trace',
      'The sum of a matrix’s diagonal entries. For projections, the trace records dimension.'),
    'rank': item('rank',
      'The number of independent output directions of a matrix; equivalently, the dimension of its image.'),
    'conjugation': item('conjugation',
      'Replacing an element x by gxg⁻¹. It changes the point of view inside the group without changing the element’s intrinsic group-theoretic behavior.'),
    'MF radical': item('MF radical',
      'The normal subgroup consisting of every element that every homomorphism into every norm matrix corona sends to the identity.')
  };

  var TERM_ALIASES = {
    'groups': 'group',
    'subgroups': 'subgroup',
    'mf groups': 'MF group',
    'homomorphisms': 'homomorphism',
    'representations': 'representation',
    'finite-matrix models': 'representation',
    'quotient': 'quotient group',
    'quotients': 'quotient group',
    'unitary matrices': 'unitary matrix',
    'projections': 'projection',
    'conjugates': 'conjugation'
  };

  Object.keys(TERM_INFO).forEach(function (term) {
    TERM_ALIASES[term.toLowerCase()] = term;
  });

  var TERM_PATTERN = new RegExp(
    '\\b(' + Object.keys(TERM_ALIASES)
      .sort(function (a, b) { return b.length - a.length; })
      .map(escapePattern).join('|') + ')\\b', 'gi');

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
    if (!host) return '';
    var copy = host.cloneNode(true);
    var formulas = copy.querySelectorAll('.katex,.tex,.texd,.dmath,.mathblock');
    for (var i = 0; i < formulas.length; i++) formulas[i].remove();
    var value = clean(copy.textContent);
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

  function localRole(token, tex, context, info, atom) {
    var t = clean(token).replace(/\u200b/g, '');
    var s = tex || '';
    if (scriptedTokenInfo(t, s, atom)) return '';
    var definition = nearbyDefinition(t, context);
    if (definition) {
      return 'Here, “' + t + '” is the name introduced for ' + definition + '.';
    }

    if ((t === 'G' || t === 'H' || t === 'W') && isFullRadicalFormula(s)) {
      return 'Here, ' + t + ' is the entire group under study.';
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
    if (t === 'N' && /\\trianglelefteq|\\triangleleft/.test(s)) {
      return 'Here, N is the normal subgroup whose elements are treated as the identity when the quotient is formed.';
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
      return '';
    }
    return '';
  }

  function item(name, meaning) {
    return { name: name, meaning: meaning };
  }

  function sourceHas(tex, pattern) {
    return pattern.test(tex || '');
  }

  function adjacentScript(atom) {
    if (!atom) return null;
    var next = atom.nextElementSibling;
    return next && next.classList && next.classList.contains('msupsub') ? next : null;
  }

  function scriptKind(tex, token) {
    var source = compactTex(tex);
    var t = clean(token).replace(/−/g, '-');
    if (t === '-1' && /\^\{?-1\}?/.test(source)) return 'superscript';
    if (t === '*' && /\^\{?(?:\\ast|\*)\}?/.test(source)) return 'superscript';
    if (new RegExp('\\^\\{?' + escapePattern(t) + '\\}?').test(source)) return 'superscript';
    return 'subscript';
  }

  function scriptItem(token, base, kind, tex, scriptText) {
    var t = clean(token).replace(/\u200b/g, '');
    var b = clean(base).replace(/\u200b/g, '');
    var script = clean(scriptText).replace(/\u200b/g, '');

    if (kind === 'superscript') {
      if (t === '−1' || t === '-1') return item('inverse',
        'The exponent −1 means “undo this operation.” For a group element or invertible matrix, it denotes the inverse.');
      if (t === '*' || t === '∗') return item('adjoint',
        'The star in the upper-right denotes the adjoint: transpose the matrix and complex-conjugate its entries.');
      return item('exponent ' + t,
        'An upper-right exponent records a power or another operation applied to the base symbol.');
    }

    if (b === 'Rad' && t === 'MF') return item('the MF subscript',
      'The subscript specifies which target representations define the radical. Here only homomorphisms into norm matrix coronas are used.');
    if (b === 'W' && t === 'Q') return item('the quotient label Q',
      'The subscript says which visible quotient was prescribed when the group W_Q was constructed.');
    if (b === 'π' && t === 'Q') return item('the quotient label Q',
      'The subscript identifies π_Q as the canonical quotient map onto Q.');
    if (b === 'd' && t === 'n') return item('the stage n',
      'The subscript selects the n-th matrix size in the sequence d₁,d₂,d₃,….');
    if (b === 'M' && (t === 'd' || /^d\s*n?$/.test(t + script))) return item('the matrix size',
      'The subscript gives the size of the square matrix algebra. M_{d_n} consists of all d_n-by-d_n complex matrices.');
    if (b === 'F' && t === '2') return item('the two-element field',
      'The subscript 2 says this field has exactly two elements, 0 and 1, with 1 + 1 = 0.');
    if (b === 'EL' && /^\d+$/.test(t)) return item('the matrix rank',
      'This subscript gives the number of rows and columns in the elementary matrices that generate the group.');
    if ((t === 'G' || t === 'H' || t === 'W') && /\\normal[^_]*_/.test(tex)) {
      return item('the ambient-group subscript',
        'This subscript says that the normal closure is taken inside ' + t + ', using conjugation by elements of ' + t + '.');
    }
    if (b === 'tr') return item('the trace normalization',
      'The subscript specifies the matrix dimension used to normalize the trace.');
    return item('subscript ' + t,
      'A lower-right subscript labels which member of a family is meant; it is not multiplication.');
  }

  function scriptedTokenInfo(token, tex, atom) {
    if (!atom || !atom.closest) return null;
    var scriptBox = atom.closest('.msupsub');
    if (scriptBox) {
      var baseNode = scriptBox.previousElementSibling;
      var base = baseNode ? baseNode.textContent : '';
      return scriptItem(token, base, scriptKind(tex, token), tex, scriptBox.textContent);
    }

    var attached = adjacentScript(atom);
    if (!attached) return null;
    var attachedText = clean(attached.textContent);
    if (token === 'M') return item('matrix algebra',
      'M with a size in the subscript denotes all square complex matrices of that size.');
    if (token === 'd' && /n/.test(attachedText)) return item('matrix dimension',
      'The symbol d_n is the size of the finite matrices used at stage n.');
    return null;
  }

  function compactTex(tex) {
    return String(tex || '').replace(/\s+/g, '');
  }

  function isFullRadicalFormula(tex) {
    var match = compactTex(tex).match(
      /(?:\\Rad|\\operatorname\{Rad\})_\{?\\mathrm\{MF\}\}?\(([^()]+)\)=([^=]+)$/);
    return !!match && match[1] === match[2];
  }

  function explainToken(token, tex, atom) {
    var t = clean(token).replace(/\u200b/g, '');
    var scripted = scriptedTokenInfo(t, tex, atom);
    if (scripted) return scripted;

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
      return null;
    }
    if (t === '⟨' || t === '⟩') {
      if (sourceHas(tex, /\\langle\s*[^,]+\\rangle/)) return item('generated subgroup',
        'The angle brackets mean the smallest subgroup containing the listed element or elements.');
      return null;
    }
    if (t === '(' || t === ')' || t === '{' || t === '}' || t === ',') return null;
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
    if (t === 'N' && sourceHas(tex, /\\mathbb\s*\{N\}|\\N\b/)) return item('the natural numbers',
      'The counting numbers 0,1,2,3,… (or, by some conventions, starting at 1).');
    if (t === 'N' && sourceHas(tex, /N\s*(?:\\trianglelefteq|\\triangleleft)|\/[{]?N[}]?/)) return item('the normal subgroup N',
      'This is the subgroup being collapsed to the identity in the quotient. Normality ensures that the quotient multiplication is well-defined.');
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
      q: ['a complementary projection or quotient label', 'In projection formulas it selects a complementary invariant sector; as a subscript it can label a quotient.'],
      n: ['an index', 'Usually the stage of a matrix sequence or a matrix dimension.'],
      i: ['an index', 'A label selecting a row, column, generator, or term.'],
      j: ['an index', 'A second label selecting a row, column, generator, or term.'],
      x: ['an element', 'A generic member of a group, ring, or space.'],
      g: ['a group element', 'A generic reversible operation in the group.'],
      h: ['a subgroup element', 'A generic element of the subgroup under discussion.']
    };
    if (named[t]) return item(named[t][0], named[t][1]);

    return null;
  }

  function explainFormula(tex) {
    var s = tex || '';
    if (isFullRadicalFormula(s)) return 'Every homomorphism from this group to every MF group sends every element to the identity. Thus, if the group is nontrivial, it is not MF.';
    if (/\\Rad_/.test(s) && /\\ker/.test(s) && /\\normal/.test(s)) return 'This computes exactly what finite-matrix models cannot detect: the kernel of the quotient map, which is also the normal subgroup generated by the displayed element. The quotient is everything that remains visible to MF groups.';
    if (/\\Rad_/.test(s) && /=/.test(s)) return 'The MF radical consists of the elements erased by every homomorphism into every norm matrix corona. This equation identifies that invisible subgroup exactly.';
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
    return '';
  }

  function addsFormulaInformation(token, explanation) {
    var t = clean(token).replace(/\u200b/g, '');
    if (!explanation) return false;
    if ((t === '⊴' || t === '◁') && /normal subgroup/.test(explanation)) return false;
    if ((t === '≤' || t === '⊆') && /containment statement/.test(explanation)) return false;
    if ((t === '≅' || t === '≃') && /same mathematical structure/.test(explanation)) return false;
    if ((t === '↪') && /embeds faithfully/.test(explanation)) return false;
    if ((t === '↠') && /reaches every element/.test(explanation)) return false;
    if ((t === '→' || t === '⟶') && /describes a map/.test(explanation)) return false;
    return true;
  }

  function canonicalTerm(term) {
    return TERM_ALIASES[clean(term).toLowerCase()] || '';
  }

  function explainTerm(term) {
    var canonical = canonicalTerm(term);
    return canonical ? TERM_INFO[canonical] : null;
  }

  function setLinkedText(node, value, excludedTerm) {
    node.textContent = '';
    var text = String(value || '');
    var cursor = 0;
    TERM_PATTERN.lastIndex = 0;
    var match;
    while ((match = TERM_PATTERN.exec(text))) {
      if (match.index > cursor) {
        node.appendChild(document.createTextNode(text.slice(cursor, match.index)));
      }
      var canonical = canonicalTerm(match[0]);
      if (!canonical || canonical === excludedTerm) {
        node.appendChild(document.createTextNode(match[0]));
      } else {
        var button = document.createElement('button');
        button.type = 'button';
        button.className = 'math-term-help';
        button.setAttribute('data-term', canonical);
        button.textContent = match[0];
        node.appendChild(button);
      }
      cursor = TERM_PATTERN.lastIndex;
    }
    if (cursor < text.length) node.appendChild(document.createTextNode(text.slice(cursor)));
  }

  function renderExplanation(state) {
    var box = ensurePanel();
    currentExplanation = state;
    box.querySelector('.math-explainer-symbol').textContent = state.symbol;
    box.querySelector('#math-explainer-title').textContent = state.info.name;
    setLinkedText(box.querySelector('.math-explainer-meaning'),
      state.info.meaning, state.term || '');

    var localBox = box.querySelector('.math-explainer-local');
    setLinkedText(localBox, state.local || '', state.term || '');
    localBox.hidden = !state.local;

    var formulaBox = box.querySelector('.math-explainer-formula');
    setLinkedText(formulaBox, state.formula || '', state.term || '');
    formulaBox.hidden = !state.showFormula;

    box.querySelector('.math-explainer-back').hidden = explanationHistory.length === 0;
    box.hidden = false;
  }

  function openTerm(term) {
    var canonical = canonicalTerm(term);
    var info = explainTerm(canonical);
    if (!info) return;
    if (currentExplanation) explanationHistory.push(currentExplanation);
    renderExplanation({
      symbol: canonical,
      info: info,
      local: '',
      formula: '',
      showFormula: false,
      term: canonical
    });
  }

  function goBack() {
    if (!explanationHistory.length) return;
    renderExplanation(explanationHistory.pop());
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
      '<p class="math-explainer-meaning"></p>' +
      '<p class="math-explainer-local"></p>' +
      '<p class="math-explainer-formula"></p>';
    document.body.appendChild(panel);
    panel.querySelector('.math-explainer-back').addEventListener('click', goBack);
    panel.querySelector('.math-explainer-close').addEventListener('click', closePanel);
    return panel;
  }

  function openExplanation(atom, math) {
    var token = clean(atom && atom.textContent) || 'formula';
    var tex = texOf(math);
    var info = explainToken(token, tex, atom);
    if (!info) return;
    var context = nearbyText(math);
    var local = localRole(token, tex, context, info, atom);
    var formula = explainFormula(tex);
    explanationHistory = [];
    renderExplanation({
      symbol: token,
      info: info,
      local: local,
      formula: formula,
      showFormula: addsFormulaInformation(token, formula),
      term: ''
    });
    lastFormula = math;
  }

  function closePanel() {
    if (!panel) return;
    panel.hidden = true;
    explanationHistory = [];
    currentExplanation = null;
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
      var tex = texOf(math);
      for (var j = 0; j < atoms.length; j++) {
        var atom = atoms[j];
        if (!clean(atom.textContent)) continue;
        if (atom.querySelector(ATOM_SELECTOR)) continue;
        if (!explainToken(clean(atom.textContent), tex, atom)) continue;
        atom.classList.add('math-symbol-help');
      }
    }
  }

  function addPrompt() {
    if (document.querySelector('.math-help-prompt')) return;
    var anchor = document.querySelector('.paper-key, .paper-head, nav.top, header');
    if (!anchor || !document.querySelector('.katex')) return;
    var prompt = document.createElement('p');
    prompt.className = 'math-help-prompt';
    prompt.textContent = 'Math is interactive — click any symbol for plain English.';
    if (anchor.classList.contains('paper-key')) anchor.insertAdjacentElement('afterend', prompt);
    else anchor.insertAdjacentElement('afterend', prompt);
  }

  document.addEventListener('click', function (event) {
    var term = event.target.closest && event.target.closest('.math-term-help');
    if (term) {
      event.preventDefault();
      event.stopPropagation();
      openTerm(term.getAttribute('data-term'));
      return;
    }
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
    explainTerm: explainTerm,
    scriptInfo: function (token, base, kind, tex, scriptText) {
      return scriptItem(token, base, kind, tex, scriptText || token);
    },
    localRole: function (token, tex, context) {
      return localRole(token, tex, context, explainToken(token, tex, null), null);
    },
    decorate: decorate
  };
}());
