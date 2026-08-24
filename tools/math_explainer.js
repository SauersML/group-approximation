(function () {
  'use strict';

  if (window.__cairnMathExplainerInstalled) return;
  window.__cairnMathExplainerInstalled = true;

  var panel;
  var lastObject;
  var history = [];
  var current;

  /* These entries are used only when a reader follows a word inside an
     explanation. Formula clicks are handled by the contextual rules below. */
  var TERMS = {
    'group': entry('group',
      'A collection of reversible operations. The operations can be combined, there is a do-nothing operation, and every operation can be undone.'),
    'subgroup': entry('subgroup',
      'A collection of operations inside a larger group that is itself a group.'),
    'normal subgroup': entry('normal subgroup',
      'A subgroup that remains the same when the larger group changes coordinates by conjugation. Exactly these subgroups can be collapsed to form quotient groups.'),
    'MF group': entry('MF group',
      'A group that can be represented faithfully by larger and larger finite unitary matrices, with every multiplication error tending to zero in operator norm.'),
    'homomorphism': entry('homomorphism',
      'A map that preserves multiplication and the do-nothing element. It translates one group into another without changing the group laws.'),
    'representation': entry('representation',
      'A homomorphism that realizes abstract group operations as concrete matrices or operators.'),
    'identity': entry('identity',
      'The do-nothing element. A representation erases an element when it sends that element to the identity.'),
    'kernel': entry('kernel',
      'All elements erased by a homomorphism—that is, all elements sent to the identity.'),
    'quotient group': entry('quotient group',
      'The group left after every element of a chosen normal subgroup is declared to be the identity.'),
    'norm matrix corona': entry('norm matrix corona',
      'An object made from sequences of finite matrices. Two sequences represent the same object when their operator-norm difference tends to zero.'),
    'operator norm': entry('operator norm',
      'The greatest amount by which a matrix can stretch a vector. Small operator norm means small in every direction.'),
    'unitary matrix': entry('unitary matrix',
      'A matrix that preserves lengths and angles. Its inverse is its conjugate transpose.'),
    'projection': entry('projection',
      'An operator that keeps one chosen subspace and sends all perpendicular directions to zero.'),
    'trace': entry('trace',
      'The sum of a matrix’s diagonal entries. On a projection, it measures the dimension of the selected subspace.'),
    'rank': entry('rank',
      'The dimension of the output space of a matrix: the number of independent directions that survive.'),
    'conjugation': entry('conjugation',
      'Replacing x by gxg⁻¹. This changes coordinates inside a group while preserving the group-theoretic nature of x.'),
    'property (T)': entry('property (T)',
      'A rigidity property: if a unitary action has vectors that are almost fixed by a suitable finite test set, then it has a genuinely fixed vector.'),
    'MF radical': entry('MF radical',
      'The normal subgroup made of all elements erased by every homomorphism into every norm matrix corona.'),
    'Leavitt algebra': entry('Leavitt algebra',
      'An algebra containing algebraic maps that identify one free module with two copies of itself. This self-copy structure supplies the compression in the paper.'),
    'elementary matrix': entry('elementary matrix',
      'The identity matrix with one extra off-diagonal entry. Such matrices generate the elementary linear group.')
  };

  var ALIASES = {
    'groups': 'group',
    'subgroups': 'subgroup',
    'mf groups': 'MF group',
    'homomorphisms': 'homomorphism',
    'representations': 'representation',
    'kernels': 'kernel',
    'quotient': 'quotient group',
    'quotients': 'quotient group',
    'norm matrix coronas': 'norm matrix corona',
    'unitary matrices': 'unitary matrix',
    'projections': 'projection',
    'ranks': 'rank',
    'conjugates': 'conjugation',
    'kazhdan property': 'property (T)',
    'binary leavitt algebra': 'Leavitt algebra',
    'elementary matrices': 'elementary matrix'
  };

  Object.keys(TERMS).forEach(function (term) {
    ALIASES[term.toLowerCase()] = term;
  });

  var TERM_PATTERN = new RegExp(
    '\\b(' + Object.keys(ALIASES)
      .sort(function (a, b) { return b.length - a.length; })
      .map(escapePattern).join('|') + ')\\b', 'gi');

  function entry(name, explanation, detail) {
    return { name: name, explanation: explanation, detail: detail || '' };
  }

  function clean(value) {
    return String(value || '').replace(/\u200b/g, '').replace(/\s+/g, ' ').trim();
  }

  function compact(value) {
    return String(value || '').replace(/\s+/g, '');
  }

  function escapePattern(value) {
    return String(value || '').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
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
    if (value.length > 360) value = value.slice(0, 357).replace(/\s+\S*$/, '') + '…';
    return value;
  }

  function has(tex, pattern) {
    return pattern.test(tex || '');
  }

  function formulaGroup(tex, fallback) {
    var match = compact(tex).match(/(?:\\Rad|\\operatorname\{Rad\})_\{?\\mathrm\{MF\}\}?\(([^()]+)\)/);
    return match ? match[1].replace(/[{}\\]/g, '') : fallback;
  }

  function isFullRadicalFormula(tex) {
    var match = compact(tex).match(
      /(?:\\Rad|\\operatorname\{Rad\})_\{?\\mathrm\{MF\}\}?\(([^()]+)\)=([^=]+)$/);
    return !!match && match[1] === match[2];
  }

  function formulaExplanation(tex) {
    var s = compact(tex);
    if (/\\mathcalQ_\{?\\mathbfd\}?=.*\\prod.*\\bigoplus/.test(s)) {
      return 'For each stage n, choose a size d_n and take a complex matrix of that size. The product keeps every bounded sequence of those matrices. Dividing by the direct sum declares two sequences equivalent when their operator-norm difference tends to zero. The result records exactly the matrix behavior that persists in the limit.';
    }
    if (/\\bigoplus_nM_\{d_n\}.*=\\\{.*\\opnorm\{x_n\}\\longrightarrow0/.test(s)) {
      return 'This is the part discarded in the matrix corona: sequences of matrices whose operator norms tend to zero. Such a sequence becomes zero in the quotient because it disappears uniformly in every direction.';
    }
    if (/\\Rad_\{\\mathrm\{MF\}\}\([^)]*\)=\\bigcap/.test(s)) {
      return 'Take every possible sequence of matrix sizes and every homomorphism into the corresponding norm matrix corona. Each kernel is what one such finite-matrix model erases. Their intersection is what all finite-matrix models erase.';
    }
    if (isFullRadicalFormula(s)) {
      var group = formulaGroup(s, 'the group');
      return 'The MF radical is all of ' + group + '. Therefore every homomorphism from ' + group + ' to every MF group sends every element to the identity; if ' + group + ' is nontrivial, it is not MF.';
    }
    if (/\\Rad_\{\\mathrm\{MF\}\}\(W_Q\)=\\pi_Q\^\{-1\}/.test(s)) {
      return 'An element of W_Q is invisible to every finite-matrix limit exactly when its image in Q is already invisible there. The construction adds no new MF-visible information beyond Q.';
    }
    if (/\\Rad_\{\\mathrm\{MF\}\}\(W_Q\)=\\ker\\pi_Q=\\normal/.test(s)) {
      return 'When Q is MF, the only elements invisible to finite-matrix limits are those killed by the quotient map. They form exactly the normal subgroup generated by d.';
    }
    if (/uLu\^\{-1\}\\leL|\\tauL\\tau\^\{-1\}\\leL/.test(s)) {
      return 'Conjugation by the displayed element carries L onto a copy contained inside L. This one-sided self-compression is what turns a centralizing element into the obstruction used later.';
    }
    if (/\\operatorname\{Comp\}_G\(L\)/.test(s)) {
      return 'Comp_G(L) collects exactly the elements of G whose conjugation sends L into L. They are the available one-sided compressions of L.';
    }
    if (/\\mathfrakD_G\(L\)=\\normal/.test(s)) {
      return 'This defines the compression defect. Start with every commutator obtained by compressing an element that originally commutes with L, then include every conjugate and product needed to make a normal subgroup. The result measures everything that the compression can force finite-matrix models to erase.';
    }
    if (/K\\trianglelefteqG/.test(s) && /K\\le\\Rad_\{\\mathrm\{MF\}\}\(G\)/.test(s)) {
      return 'If the normal property-(T) subgroup K lies inside the compression defect, then every finite-matrix-limit representation sends every element of K to the identity.';
    }
    if (/t_is_j=\\delta_\{ij\}/.test(s) || /s_0t_0\+s_1t_1=1/.test(s)) {
      return 'These are the binary Leavitt relations. The first makes t_i reverse the corresponding s_i and annihilate the other branch. The second says the two branch projections together fill the whole algebra. Algebraically, one copy of the module has been split into two complete copies.';
    }
    if (/H=\\EL_\{?12\}?\(R\)/.test(s)) {
      return 'H is generated by 12-by-12 elementary matrices with entries in the binary Leavitt algebra R. This is the paper’s concrete simple property-(T) group whose entire MF radical is H.';
    }
    if (/L=\\EL_\{?3\}?\(R\)/.test(s)) {
      return 'L is the 3-by-3 elementary-matrix subgroup in the upper-left corner of H. It has property (T), and the matrix τ conjugates it into a smaller copy of itself.';
    }
    if (/d=\[\\tau.*c.*\\tau\^\{-1\}.*\\ell\]/.test(s)) {
      return 'The element d measures the failure of the moved element τcτ⁻¹ to commute with ℓ. Before c is moved it commutes with all of L; after the one-sided compression, this commutator becomes the nontrivial obstruction.';
    }
    if (/d=e_\{?02\}?\(q\)/.test(s)) {
      return 'The commutator d is computed explicitly as the elementary matrix e_02(q). Since the Leavitt coefficient q is nonzero, d is not the identity.';
    }
    if (/W_Q=B\*_A\(Q\\timesA\)/.test(s)) {
      return 'W_Q glues B to Q × A by identifying their copies of A. The B part is invisible to all MF targets, while Q is the prescribed part that remains visible.';
    }
    if (/\\pi_Q\\colonW_Q\\longrightarrowQ/.test(s)) {
      return 'The map π_Q deletes the attached B part and the A coordinate, leaving Q. It is onto, and Q sits back inside W_Q, so the quotient is split.';
    }
    if (/\\operatorname\{Hom\}\(Q,T\).*\\operatorname\{Hom\}\(W_Q,T\)/.test(s)) {
      return 'Every homomorphism from W_Q to T is obtained in exactly one way from a homomorphism Q → T. Thus T cannot detect any additional information in W_Q beyond Q.';
    }
    if (/\\ker\\pi_Q=\\normald_\{?W_Q\}?/.test(s)) {
      return 'The quotient map erases exactly the normal subgroup generated by d. Killing d kills the whole attached group B and leaves precisely Q.';
    }
    return '';
  }

  function compoundObject(text, tex) {
    var t = clean(text);
    var s = compact(tex);
    if (/^RadMF$/.test(t)) {
      var group = formulaGroup(s, 'the group inside the parentheses');
      return entry('the MF radical of ' + group,
        'This is the normal subgroup of ' + group + ' consisting of every element that every homomorphism into every norm matrix corona sends to the identity. It is precisely the part of ' + group + ' that all operator-norm finite-matrix limits fail to detect.');
    }
    if (/^Qd$/.test(t) && /\\mathcalQ_\{?\\mathbfd\}?/.test(s)) {
      return entry('the norm matrix corona Q_d',
        'The bold d is the whole sequence of matrix sizes d₁,d₂,d₃,…. Q_d packages bounded sequences of matrices of those sizes and treats a sequence as zero when its operator norm tends to zero. A group is MF when it embeds faithfully into the unitary elements of some Q_d.');
    }
    if (/^Mdn$/.test(t) || (/^Md/.test(t) && /M_\{d_n\}/.test(s))) {
      return entry('the n-th matrix algebra',
        'M_{d_n}(C) is the algebra of all d_n-by-d_n matrices with complex entries. It is the finite matrix model used at stage n; the sizes d_n may grow with n.');
    }
    if (/^dn$/.test(t) && /d_n/.test(s)) {
      return entry('the matrix size d_n',
        'This positive integer is the number of rows and columns in the finite matrices used at stage n. The sequence of all these sizes is written in bold as d.');
    }
    if (/^EL\d+$/.test(t)) {
      var size = t.replace('EL', '');
      return entry('the elementary group of rank ' + size,
        'This group is generated by ' + size + '-by-' + size + ' identity matrices with one extra off-diagonal entry from R. Multiplying these elementary matrices encodes addition and multiplication in the coefficient algebra R.');
    }
    if (/^GL\d+$/.test(t)) {
      var rank = t.replace('GL', '');
      return entry('the invertible ' + rank + '-by-' + rank + ' matrices',
        'GL_' + rank + '(R) is the group of every invertible ' + rank + '-by-' + rank + ' matrix with entries in R. The elementary group EL_' + rank + '(R) is the subgroup generated by elementary matrices.');
    }
    if (/^e\d\d$/.test(t) || /^eij$/.test(t)) {
      var indices = t.slice(1);
      return entry('the elementary matrix e_' + indices,
        'This is the identity matrix with one extra off-diagonal entry in the position named by the two indices. In e_02(q), that extra entry is q; because q is nonzero, this matrix is not the identity.');
    }
    if (/^WQ$/.test(t)) {
      return entry('the group W_Q built over Q',
        'W_Q is formed by attaching the MF-invisible group B to the chosen group Q along the cyclic subgroup generated by d. Every homomorphism from W_Q to an MF group factors through Q, so Q contains all of the information that finite-matrix limits can see.');
    }
    if (/^πQ$/.test(t)) {
      return entry('the quotient map π_Q',
        'This homomorphism sends W_Q onto Q. It deletes the attached invisible part, and its kernel is exactly the normal subgroup generated by d.');
    }
    if (/^(?:CompG|CompGL)$/.test(t) || (/\\operatorname\{Comp\}_G\(L\)/.test(s) && /^Comp/.test(t))) {
      return entry('the elements that compress L',
        'Comp_G(L) consists of those elements u in G for which conjugation sends L into L. Such a u need not carry L onto all of L; the one-sided inclusion is the source of the obstruction.');
    }
    if (/^[D𝔇]G$/.test(t) && /\\mathfrakD_G/.test(s)) {
      return entry('the compression defect inside G',
        'This normal subgroup is generated by commutators created when a one-sided compression moves elements that originally commute with L. The theorem proves that normal property-(T) subgroups lying here are erased by every MF representation.');
    }
    if (/^pK$/.test(t) && /p_K/.test(s)) {
      return entry('the Kazhdan projection of K',
        'This projection selects exactly the vectors fixed by every element of K. Property (T) makes this fixed-vector selector an actual element of the maximal group C*-algebra rather than a projection chosen separately in each representation.');
    }
    if (/^[∏Π]n$/.test(t) && /\\prod_nM_\{d_n\}/.test(s)) {
      return entry('all bounded matrix sequences',
        'The product contains one matrix from M_{d_n}(C) at every stage n, with a uniform bound on their operator norms. Multiplication and addition are performed coordinate by coordinate.');
    }
    if (/^[⊕⨁]n$/.test(t) && /\\bigoplus_nM_\{d_n\}/.test(s)) {
      return entry('the sequences that vanish',
        'This direct sum consists of matrix sequences whose operator norms tend to zero. The quotient removes exactly these vanishing errors.');
    }
    if ((t === '*' || /^[*∗]A$/.test(t)) && /B\*_A\(Q\\timesA\)/.test(s)) {
      return entry('gluing the two groups along A',
        'The amalgamated free product joins B and Q × A while identifying the copy of A in each. Apart from that identification, it adds no relations between the two sides.');
    }
    if (/^⋂d$/.test(t) && /\\bigcap_\{?\\mathbfd\}?/.test(s)) {
      return entry('the intersection over every matrix-size sequence',
        'The bold d ranges over every possible sequence of finite matrix sizes. An element survives this intersection only if every choice of matrix sizes fails to detect it.');
    }
    if (/^⋂π/.test(t) && /\\bigcap_\{?\\pi\\colonG\\to\\U\(\\mathcalQ/.test(s)) {
      return entry('the intersection over every corona representation',
        'For the chosen matrix sizes, π ranges over every homomorphism from G into the unitary elements of the matrix corona. Intersecting their kernels keeps exactly the elements that all of these representations erase.');
    }
    if (t === '×' && /Q\\timesA/.test(s)) {
      return entry('the product Q × A',
        'An element is a pair: one element of Q and one element of A. The two coordinates multiply independently. The quotient map π_Q keeps the Q coordinate and discards A.');
    }
    if (/^Hom$/.test(t)) {
      return entry('all homomorphisms to the target',
        'Hom(source,target) is the complete collection of multiplication-preserving maps from the source group to the target group. The displayed bijection says the two sources have exactly the same maps into T.');
    }
    if (/^ker$/.test(t)) {
      return entry('the kernel of the map',
        'The kernel is every group element sent to the identity. It records exactly which information the map erases.');
    }
    if (/^U$/.test(t) && /\\U\(\\mathcalQ/.test(s)) {
      return entry('the unitary elements of the matrix corona',
        'These are the elements represented by sequences of finite unitary matrices. They form a group under multiplication, and MF representations take their values here.');
    }
    if (t === 'C' && /\\C/.test(s)) {
      return entry('the complex numbers',
        'These are numbers with real and imaginary parts. The finite matrix algebras in the MF definition use complex entries because unitary matrices naturally live over the complex numbers.');
    }
    if (/^F2$/.test(t) && /\\F_?\{?2\}?/.test(s)) {
      return entry('the two-element field F₂',
        'This number system contains only 0 and 1, with 1 + 1 = 0. Its only nonzero scalar is 1; that fact makes the center of the concrete elementary group trivial in the simplicity proof.');
    }
    if (/^LF2$/.test(t) && /L_\{?\\F_?\{?2\}?\}?/.test(s)) {
      return entry('the binary Leavitt algebra',
        'L_{F₂}(1,2) is the algebra generated by s₀,s₁,t₀,t₁ with the displayed Leavitt relations. Those relations algebraically identify one free module with two copies of itself, which makes the one-sided matrix compression possible.');
    }
    return null;
  }

  function namedObject(text, tex, context) {
    var t = clean(text);
    var s = compact(tex);
    if (t === 'd' && !/d_n|\\mathbfd/.test(s)) {
      return entry('d, the explicit obstruction element',
        'Here d is the nonidentity element [τcτ⁻¹,ℓ], later computed as the elementary matrix e_02(q). It lies in the compression defect. Because H is simple, the normal subgroup generated by d is all of H, so proving that every MF representation erases d forces every such representation of H to be trivial.');
    }
    if (t === 'q' && /e_\{?02\}?\(q\)|q=s_?\{?1\}?t_?\{?1\}?/.test(s)) {
      return entry('q, the second Leavitt corner',
        'Here q = s₁t₁. It is a nonzero idempotent in the binary Leavitt algebra. It is the coefficient in d = e_02(q), so its nonzero value proves that d is not the identity.');
    }
    if (t === 'H') {
      return entry('H, the group proved non-MF',
        'H is EL_12(R), generated by 12-by-12 elementary matrices over the binary Leavitt algebra R. The paper proves that H is nontrivial and simple, has property (T), and that every homomorphism from H to every MF group is trivial.');
    }
    if (t === 'G') {
      return entry('G, the group being tested',
        'G denotes the countable group whose finite-matrix behavior this statement studies. The nearby hypotheses specify subgroups and compression data inside G; the conclusion determines which elements every MF representation of G must erase.');
    }
    if (t === 'L') {
      return entry('L, the subgroup compressed into itself',
        'L is a property-(T) subgroup of G. A chosen element conjugates L into a copy contained in L. Its fixed-vector rigidity lets the proof transfer commutation information across that one-sided compression.');
    }
    if (t === 'K') {
      return entry('K, the normal rigid subgroup',
        'K is assumed to be a normal subgroup with property (T) and to lie inside the compression defect. The theorem concludes that every homomorphism from G into every norm matrix corona sends all of K to the identity.');
    }
    if (t === 'B' && /W_Q|Q\\timesA|B\*_A/.test(s)) {
      return entry('B, the part invisible to MF groups',
        'B is a group for which every homomorphism into every MF group is trivial. It is attached to Q to build W_Q, but no MF target can detect the attached B part.');
    }
    if (t === 'Q' && /W_Q|\\pi_Q|Q\\timesA|\\Rad.*\(Q\)/.test(s)) {
      return entry('Q, the quotient that remains visible',
        'Q is any chosen countable group. The construction W_Q adds an MF-invisible part to Q without changing any homomorphism into an MF target; the map π_Q recovers Q from W_Q.');
    }
    if (t === 'A' && /B\*_A|Q\\timesA|A=\\langle/.test(s)) {
      return entry('A, the cyclic subgroup used for gluing',
        'A is the subgroup generated by d. The construction identifies this same subgroup inside B and inside Q × A, which makes killing d collapse the attached B part and leave Q.');
    }
    if (t === 'R' && (/L_\{\\F_2\}\(1,2\)|\\EL_\{?(?:3|12)\}?\(R\)/.test(s) || /Leavitt/i.test(context))) {
      return entry('R, the binary Leavitt algebra',
        'R is the coefficient algebra L_{F₂}(1,2). Its generators split one algebraic copy into two complete copies. That self-copy structure is used to build the matrix τ that compresses L into itself.');
    }
    if (t === 'τ') {
      return entry('τ, the matrix that performs the compression',
        'τ is an explicit invertible 12-by-12 elementary matrix. Conjugating by τ sends L = EL_3(R) into a copy contained in L. It also moves c so that the commutator with ℓ becomes the nontrivial element d.');
    }
    if (t === 'u') {
      return entry('u, an element that compresses L',
        'Conjugating by u sends every element of L back into L. The image may be a proper copy, so this operation can preserve more commutation after compression than before it.');
    }
    if (t === 'c') {
      return entry('c, an element that initially commutes with L',
        'Every element of L commutes with c. After c is moved by the compressing element, that commutation can fail; the resulting commutators generate the compression defect.');
    }
    if (t === 'ℓ') {
      return entry('ℓ, a test element of L',
        'The element ℓ is chosen from L and compared with the moved element ucu⁻¹. Their commutator measures whether the original commutation with L survived the one-sided compression.');
    }
    if (t === 'π' && /\\pi\\colonG\\to\\U\(\\mathcalQ/.test(s)) {
      return entry('π, one possible finite-matrix-limit representation',
        'Here π is any homomorphism from G into the unitary elements of a norm matrix corona. Its kernel is the part of G erased by this particular representation; the MF radical intersects those kernels over every possible π.');
    }
    if (t === 'π' && /\\pi\\colonL\\to\\U\(B\)/.test(s)) {
      return entry('π, the unitary representation of L',
        'This homomorphism realizes each element of L as a unitary element of B. It extends to the maximal group C*-algebra, where the Kazhdan projection selects the vectors fixed by L.');
    }
    if (t === 'ρ' && /\\rho\\colonG\\to\\GL\(V\)/.test(s)) {
      return entry('ρ, a finite-dimensional linear representation',
        'ρ turns every element of G into an invertible linear map on the finite-dimensional space V. The commutant argument proves that every such ρ erases the compression defect.');
    }
    if (t === 'ρ' && /\\rho\\colonG\\to\\U\(\\mathcalQ/.test(s)) {
      return entry('ρ, a representation in the matrix corona',
        'ρ assigns to every element of G a sequence of finite unitary matrices, considered up to errors that vanish in operator norm. Because ρ preserves multiplication in the quotient, its coordinates are asymptotic finite-matrix models of G.');
    }
    if (t === 'Θ' && /\\Theta\\colonG\\to\\U\(\\mathcalQ/.test(s)) {
      return entry('Θ, the hypothetical representation that detects K',
        'The proof assumes that Θ is a homomorphism into a norm matrix corona and that some element of K is not sent to the identity. The complementary Kazhdan corner is then used to derive a contradiction.');
    }
    if (t === 'N' && /N\\trianglelefteqG|G\/N|\\operatorname\{cl\}.*\(N\)/.test(s)) {
      return entry('N, the subgroup being collapsed',
        'N is any normal subgroup of G. Forming G/N declares every element of N to be the identity. The MF-closure statement asks whether finite-matrix representations force any additional elements to disappear.');
    }
    if (t === 'M' && /M\\text\{MF\}|G\\toM|W_Q.*M/.test(s)) {
      return entry('M, an arbitrary MF target',
        'M can be any MF group. Proving that every homomorphism into every such M is trivial means that finite-matrix limits cannot see any nonidentity element of the source group.');
    }
    if (t === 'T' && /\\operatorname\{Hom\}.*T|B\\toT/.test(s)) {
      return entry('T, the target group',
        'T is the group receiving the homomorphisms in this statement. The hypothesis that B has no nontrivial maps to T forces every map from W_Q to T to ignore B and pass uniquely through Q.');
    }
    return null;
  }

  function explainObject(text, tex, context) {
    if (!text || /^[(){}\[\],.;:|‖∥⟨⟩⌈⌉⌊⌋]+$/.test(clean(text))) return null;
    return compoundObject(text, tex) || namedObject(text, tex, context || '');
  }

  function canonicalTerm(term) {
    return ALIASES[clean(term).toLowerCase()] || '';
  }

  function explainTerm(term) {
    var canonical = canonicalTerm(term);
    return canonical ? TERMS[canonical] : null;
  }

  function setLinkedText(node, value, excludedTerm) {
    node.textContent = '';
    var text = String(value || '');
    var cursor = 0;
    TERM_PATTERN.lastIndex = 0;
    var match;
    while ((match = TERM_PATTERN.exec(text))) {
      if (match.index > cursor) node.appendChild(document.createTextNode(text.slice(cursor, match.index)));
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
      '<p class="math-explainer-formula"></p>';
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
    var detail = state.info.detail || state.formula || '';
    var detailBox = box.querySelector('.math-explainer-formula');
    setLinkedText(detailBox, detail, state.term || '');
    detailBox.hidden = !detail || detail === state.info.explanation;
    box.querySelector('.math-explainer-back').hidden = history.length === 0;
    box.hidden = false;
  }

  function openTerm(term) {
    var canonical = canonicalTerm(term);
    var info = explainTerm(canonical);
    if (!info) return;
    if (current) history.push(current);
    render({ symbol: canonical, info: info, formula: '', term: canonical });
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
    var tex = texOf(math);
    var info = explainObject(clean(node.textContent), tex, nearbyText(math));
    if (!info) return;
    history = [];
    render({ symbol: clean(node.textContent), info: info,
      formula: formulaExplanation(tex), term: '' });
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
      var context = nearbyText(math);
      var bases = visual.querySelectorAll('.base');
      for (var j = 0; j < bases.length; j++) {
        var children = bases[j].children;
        for (var k = 0; k < children.length; k++) {
          var node = children[k];
          if (!isTopLevelMathObject(node)) continue;
          var info = explainObject(clean(node.textContent), tex, context);
          if (!info) continue;
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
    prompt.textContent = 'Highlighted mathematical objects are clickable for an explanation of what they are and what they do here.';
    anchor.insertAdjacentElement('afterend', prompt);
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
    var object = event.target.closest && event.target.closest('.math-symbol-help');
    var math = object && object.closest('.katex');
    if (object && math) {
      event.preventDefault();
      event.stopPropagation();
      openObject(object, math);
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
        event.target.classList && event.target.classList.contains('math-symbol-help')) {
      var math = event.target.closest('.katex');
      if (math) {
        event.preventDefault();
        openObject(event.target, math);
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
    explainObject: explainObject,
    explainFormula: formulaExplanation,
    explainTerm: explainTerm,
    decorate: decorate
  };
}());
