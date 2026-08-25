(function () {
  'use strict';

  if (window.__cairnMathExplainerInstalled) return;
  window.__cairnMathExplainerInstalled = true;

  var panel;
  var lastObject;
  var history = [];
  var current;

  /* Words inside an explanation may be followed to these short definitions.
     TeX declarations supply contextual explanations; the notation table below
     supplies fixed meanings for standard symbols in those declared formulas. */
  var TERMS = {
    'set': entry('set',
      'A collection of objects. An object either belongs to the set or it does not.'),
    'element': entry('element',
      'One object belonging to a [[set]].'),
    'sequence': entry('sequence',
      'A list in a fixed order: first, second, third, and so on. A subscript such as n names a position in the list.'),
    'index': entry('index',
      'A label, often a small number written below a letter, that selects one position, row, column, or item.'),
    'function': entry('function',
      'A rule that assigns exactly one output to each allowed input. This paper also uses the word map for a function.'),
    'image': entry('image',
      'The output of a [[function]], or the [[set]] of outputs obtained from several inputs.'),
    'preimage': entry('preimage',
      'Given some outputs of a [[function]], their preimage is the [[set]] of all inputs that produce those outputs.'),
    'surjective': entry('surjective',
      'A [[function]] is surjective, or onto, when every possible output is reached by at least one input.'),
    'bijection': entry('bijection',
      'A perfect pairing between two [[set|sets]]: every object on either side is paired with exactly one object on the other side.'),
    'isomorphism': entry('isomorphism',
      'A reversible [[homomorphism]]. It shows that two [[group|groups]] have the same structure even when their elements have different names.'),
    'intersection': entry('intersection',
      'The objects shared by every [[set]] being considered.'),
    'infinite product': entry('infinite product',
      'A [[set]] of [[sequence|sequences]] made by choosing one entry from each set in an endless list of sets.'),
    'direct sum': entry('direct sum',
      'In this paper, the [[sequence|sequences]] of matrices whose sizes, measured by [[operator norm]], have [[limit]] zero.'),
    'quotient': entry('quotient',
      'A construction that declares selected differences to count as zero. Objects that differ only by one of those ignored differences are then treated as equal.'),
    'set-builder notation': entry('set-builder notation',
      'A way to describe a [[set]] using braces. The part before the colon names possible elements; the part after the colon gives the rule they must satisfy.'),
    'bounded sequence': entry('bounded sequence',
      'A [[sequence]] whose entries never grow past one fixed size.'),
    'limit': entry('limit',
      'The value that a changing quantity approaches. Saying a sequence tends to zero means its entries can be made as small as desired by going far enough along the sequence.'),
    'group': entry('group',
      'A collection of reversible moves. Two moves can be performed in succession, there is a do-nothing move, and every move can be undone.'),
    'identity': entry('identity',
      'The do-nothing [[element]] of a [[group]]. In a matrix group it is the identity matrix.'),
    'inverse': entry('inverse',
      'The move that undoes a given [[group]] move. Performing a move and then its inverse gives the [[identity]].'),
    'subgroup': entry('subgroup',
      'Some elements inside a [[group]] that include the [[identity]] and remain a group when combined with one another.'),
    'conjugation': entry('conjugation',
      'Changing a group element x by another element u to obtain \\(uxu^{-1}\\). It means do u, then x, then undo u.'),
    'normal subgroup': entry('normal subgroup',
      'A [[subgroup]] whose elements stay inside it after [[conjugation]] by any element of the larger [[group]].'),
    'homomorphism': entry('homomorphism',
      'A [[function]] between [[group|groups]] that respects succession of moves and sends the [[identity]] to the identity.'),
    'representation': entry('representation',
      'A [[homomorphism]] that replaces abstract [[group]] elements with concrete matrices or other operations.'),
    'faithful': entry('faithful',
      'A [[homomorphism]] is faithful when different inputs always have different outputs, so it loses no information.'),
    'trivial homomorphism': entry('trivial homomorphism',
      'A [[homomorphism]] that sends every input to the [[identity]], so its output carries no information about the input.'),
    'kernel': entry('kernel',
      'All inputs that a [[homomorphism]] sends to the [[identity]]. A large kernel means the map forgets many elements.'),
    'quotient group': entry('quotient group',
      'The [[group]] obtained by treating every element of a chosen [[normal subgroup]] as the [[identity]].'),
    'cyclic subgroup': entry('cyclic subgroup',
      'A [[subgroup]] made from one element by repeatedly combining that element and its [[inverse]].'),
    'normal closure': entry('normal closure',
      'The smallest [[normal subgroup]] containing the listed elements. The notation \\(\\langle\\!\\langle d\\rangle\\!\\rangle_G\\) means the normal closure of d inside G.'),
    'centralizer': entry('centralizer',
      'The [[subgroup]] of elements that commute with a chosen set: doing either move first gives the same result.'),
    'commutator': entry('commutator',
      'For elements a and b, \\([a,b]=aba^{-1}b^{-1}\\). It equals the [[identity]] exactly when doing a then b gives the same result as doing b then a.'),
    'simple group': entry('simple group',
      'A nontrivial [[group]] whose only [[normal subgroup|normal subgroups]] are the identity alone and the whole group.'),
    'matrix': entry('matrix',
      'A rectangular table of numbers or algebraic entries, arranged in rows and columns.'),
    'identity matrix': entry('identity matrix',
      'A square [[matrix]] with 1 on its main diagonal and 0 everywhere else. Multiplying by it changes nothing.'),
    'complex number': entry('complex number',
      'A number of the form \\(a+bi\\), where a and b are real numbers and \\(i^2=-1\\).'),
    'vector space': entry('vector space',
      'A collection of vectors that can be added and scaled while staying in the collection.'),
    'operator': entry('operator',
      'A [[function]] that takes a vector as input and returns a vector as output.'),
    'operator norm': entry('operator norm',
      'The largest stretch factor of a [[matrix]] or [[operator]]. A small operator norm means every input vector is changed by only a small amount.'),
    'unitary matrix': entry('unitary matrix',
      'A square [[matrix]] over the [[complex number|complex numbers]] that preserves lengths and angles. Its [[inverse]] is obtained by transposing it and replacing each entry by its complex conjugate.'),
    'ring': entry('ring',
      'A number-like system in which addition, subtraction, and multiplication are allowed, although multiplication need not commute.'),
    'field': entry('field',
      'A number system in which addition, subtraction, multiplication, and division by nonzero numbers are allowed.'),
    'Kronecker delta': entry('Kronecker delta',
      'The symbol \\(\\delta_{ij}\\): it equals 1 when the [[index|indices]] i and j are equal, and 0 when they are different.'),
    'algebra': entry('algebra',
      'A [[ring]] whose elements can also be multiplied by numbers from a chosen [[field]].'),
    'scalar': entry('scalar',
      'A number used to multiply every coordinate of a vector or every entry of a matrix.'),
    'module': entry('module',
      'A vector-space-like object whose scalars come from a [[ring]] instead of necessarily coming from a field.'),
    'free module': entry('free module',
      'A [[module]] with independent coordinate directions, analogous to ordinary coordinate space.'),
    'generated by relations': entry('generated by relations',
      'Start with named symbols and allow every expression made from them, while declaring the listed equations to be true.'),
    'elementary matrix': entry('elementary matrix',
      'An [[identity matrix]] with one additional entry away from the main diagonal.'),
    'elementary group': entry('elementary group',
      'The [[group]] formed by multiplying [[elementary matrix|elementary matrices]] of a fixed size.'),
    'property (T)': entry('property (T)',
      'A rigidity feature of a [[group]]. Roughly, if the group moves some vectors only a tiny amount, then some nonzero vector must be left completely fixed.'),
    'norm matrix corona': entry('norm matrix corona',
      'An object made from [[bounded sequence|bounded sequences]] of finite [[matrix|matrices]]. Two sequences count as the same when the [[operator norm]] of their difference has [[limit]] zero.'),
    'MF group': entry('MF group',
      'A [[group]] that can be represented faithfully by increasingly large finite [[unitary matrix|unitary matrices]], with multiplication errors having [[operator norm]] that tends to zero.'),
    'MF radical': entry('MF radical',
      'The [[normal subgroup]] of elements erased by every [[homomorphism]] from the group into every [[norm matrix corona]].'),
    'Leavitt algebra': entry('Leavitt algebra',
      'A particular [[algebra]] built from four named elements \\(s_0,s_1,t_0,t_1\\) and two families of equations. Those equations let one [[free module]] behave like two copies of itself.'),
    'direct product': entry('direct product',
      'The [[group]] of ordered pairs \\((q,a)\\), with the first coordinates combined together and the second coordinates combined together.'),
    'amalgamated free product': entry('amalgamated free product',
      'A [[group]] made by joining two groups along copies of a shared [[subgroup]], without adding relations beyond those already present and the required identification.'),
    'factors through': entry('factors through',
      'A [[function]] factors through another map when it can be performed in two stages through that map. The middle output retains everything the final function needs.'),
    'closure operation': entry('closure operation',
      'A rule that enlarges a [[set]] by adding everything forced by a chosen condition, and adds nothing further when applied a second time.'),
    'pullback': entry('pullback',
      'Here, the [[preimage]] of a subgroup under a [[homomorphism]]: collect every input whose output lies in that subgroup.')
  };

  function entry(name, explanation, tex) {
    return { name: name, explanation: explanation, tex: tex || '' };
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
        tex: attrs.tex || attrs.when,
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
    return best ? entry(best.name, best.explanation, best.tex) : null;
  }

  var NOTATION = {
    '=': entry('equals sign',
      'The expression on the left and the expression on the right name the same mathematical object.', '='),
    '≠': entry('not equal',
      'The expressions on the two sides are different.', '\\ne'),
    '∈': entry('belongs to',
      'The object on the left is an [[element]] of the [[set]] or [[group]] on the right.', '\\in'),
    '≤': entry('subgroup containment',
      'In this paper, the object on the left is a [[subgroup]] contained in the [[group]] on the right. This is not a comparison of numerical size.', '\\le'),
    '→': entry('map or limit arrow',
      'Between named sets, this arrow shows the input and output of a [[function]]. After a changing quantity, it says the quantity has the stated [[limit]].', '\\longrightarrow'),
    '⟶': entry('map or limit arrow',
      'Between named sets, this arrow shows the input and output of a [[function]]. After a changing quantity, it says the quantity has the stated [[limit]].', '\\longrightarrow'),
    '↔': entry('if and only if',
      'Each statement implies the other, so the two statements are exactly equivalent.', '\\Longleftrightarrow'),
    '⇔': entry('if and only if',
      'Each statement implies the other, so the two statements are exactly equivalent.', '\\Longleftrightarrow'),
    '⟺': entry('if and only if',
      'Each statement implies the other, so the two statements are exactly equivalent.', '\\Longleftrightarrow'),
    '≅': entry('isomorphic',
      'There is an [[isomorphism]] between the two [[group|groups]]: their structure is the same after elements are renamed.', '\\cong'),
    '∩': entry('intersection sign',
      'Keep only the objects that belong to every [[set]] in the indexed family.', '\\bigcap'),
    '∏': entry('infinite-product sign',
      'Choose one entry for each value of the [[index]], producing a [[sequence]].', '\\prod'),
    '⊕': entry('direct-sum sign',
      'Here this selects the matrix [[sequence|sequences]] whose [[operator norm|operator norms]] have [[limit]] zero.', '\\bigoplus'),
    '×': entry('direct-product sign',
      'Form ordered pairs, taking one entry from each of the two [[group|groups]].', '\\times'),
    '*': entry('free-product star',
      'Join groups without imposing cross-relations. A subscript names the shared [[subgroup]] that is identified.', '*'),
    '+': entry('addition sign',
      'Add the expressions on the two sides using the addition rule of the surrounding number system, [[ring]], or [[matrix]] space.', '+'),
    '−': entry('minus sign',
      'Subtract the expression on the right, or take the additive opposite when the sign is written before one expression.', '-'),
    '/': entry('quotient slash',
      'Form a [[quotient]] by treating the objects named after the slash as zero or as the [[identity]].', '/'),
    ':': entry('such-that or map colon',
      'Inside braces it means “such that.” After a function name it introduces the function’s input and output.', ':'),
    ',': entry('separator',
      'This comma separates entries, variables, or statements in the formula.', ','),
    ';': entry('condition separator',
      'This semicolon separates a possible object from the condition it must satisfy.', ';'),
    '.': entry('end punctuation',
      'This period ends the mathematical sentence; it is not an operation.', '.'),
    '(': entry('opening parenthesis',
      'This begins a grouped expression or the input supplied to a [[function]].', '('),
    ')': entry('closing parenthesis',
      'This ends a grouped expression or the input supplied to a [[function]].', ')'),
    '{': entry('opening set brace',
      'This begins [[set-builder notation]] or a listed [[set]].', '\\{'),
    '}': entry('closing set brace',
      'This ends [[set-builder notation]] or a listed [[set]].', '\\}'),
    '[': entry('opening commutator bracket',
      'In these formulas, square brackets begin a [[commutator]].', '['),
    ']': entry('closing commutator bracket',
      'In these formulas, square brackets end a [[commutator]].', ']'),
    '1': entry('one or identity',
      'In ordinary arithmetic this is the number one. In a [[group]] or matrix formula it denotes the [[identity]].', '1'),
    '0': entry('zero',
      'The additive do-nothing value. In a [[matrix]], it means an empty entry.', '0')
  };

  var NAMED_OBJECTS = {
    'G': entry('the group G', 'G is the main [[group]] currently being discussed.', 'G'),
    'H': entry('the group H', 'H is the particular [[group]] constructed from 12-by-12 [[elementary matrix|elementary matrices]].', 'H'),
    'K': entry('the subgroup K', 'K is a [[normal subgroup]] of G that has [[property (T)]].', 'K'),
    'L': entry('the subgroup L', 'L is the [[subgroup]] to which the compression and [[property (T)]] arguments are applied.', 'L'),
    'A': entry('the subgroup A', 'A is the [[cyclic subgroup]] generated by d.', 'A'),
    'B': entry('the group B', 'B is the attached [[group]] whose [[MF radical]] is all of B.', 'B'),
    'Q': entry('the group Q', 'Q is the chosen [[group]] that remains visible to maps into [[MF group|MF groups]].', 'Q'),
    'T': entry('the target group T', 'T is the [[group]] receiving the [[homomorphism|homomorphisms]] in this statement.', 'T'),
    'M': entry('the MF target M', 'M is an [[MF group]] receiving a [[homomorphism]].', 'M'),
    'R': entry('the ring R', 'R is the [[ring]], here a binary [[Leavitt algebra]], used for matrix entries.', 'R'),
    'S': entry('the ring S', 'S is a [[ring]] used for matrix entries.', 'S'),
    'N': entry('the subgroup N', 'N is a [[normal subgroup]] whose elements will be treated as the [[identity]] in a [[quotient group]].', 'N'),
    'f': entry('the map f', 'f is the [[surjective]] [[homomorphism]] from G onto Q.', 'f'),
    'π': entry('the map pi', 'The Greek letter pi names a [[homomorphism]] or [[representation]].', '\\pi'),
    'τ': entry('the matrix tau', 'The Greek letter tau names the invertible [[matrix]] that sends L back inside itself by [[conjugation]].', '\\tau'),
    'ℓ': entry('the element ell', 'The Greek letter ell names an [[element]] of the [[subgroup]] L.', '\\ell'),
    'u': entry('the element u', 'u is a [[group]] element used for [[conjugation]].', 'u'),
    'c': entry('the element c', 'c is a [[group]] element that commutes with every element of L.', 'c'),
    'd': entry('the element d', 'd is the concrete nonidentity [[group]] element whose [[normal closure]] becomes H.', 'd'),
    'q': entry('the algebra element q', 'q is the nonzero [[Leavitt algebra]] element \\(s_1t_1\\).', 'q'),
    'a': entry('the entry a', 'a is a variable [[element]], usually an entry from the surrounding [[ring]].', 'a'),
    'x': entry('the entry x', 'x is a variable [[element]] or one term in a [[sequence]], as specified by the surrounding formula.', 'x'),
    'n': entry('the index n', 'n is an [[index]] selecting a stage, matrix size, or position in a [[sequence]].', 'n'),
    'i': entry('the index i', 'i is an [[index]], usually selecting a matrix row.', 'i'),
    'j': entry('the index j', 'j is an [[index]], usually selecting a matrix column.', 'j')
  };

  function notationExplanation(text, tex) {
    var symbol = clean(text);
    if (symbol === '∗') symbol = '*';
    if (symbol === '=') symbol = '≠';
    if (symbol === '') symbol = '≠';
    if (symbol === '⋂') symbol = '∩';
    if (symbol === '⨁') symbol = '⊕';
    if (NOTATION[symbol]) return NOTATION[symbol];
    if (symbol === 'Q' && /\\mathcal\s*Q/.test(tex || '')) return entry('the corona symbol Q',
      'The calligraphic Q is the chosen name for this [[norm matrix corona]].', '\\mathcal Q');
    if (symbol === 'C' && /\\C|\\mathbb\s*\{?C/.test(tex || '')) return entry('the complex-number symbol C',
      'The blackboard-style C names the [[complex number|complex numbers]].', '\\mathbb C');
    if (symbol === 'C' && /C_[GH]/.test(tex || '')) return entry('the centralizer symbol C',
      'Here C names a [[centralizer]] inside the group shown as its subscript.', 'C');
    if (symbol === 'M' && /M_\{?d_n/.test(tex || '')) return entry('the matrix-set symbol M',
      'M names a [[set]] of square [[matrix|matrices]]. Its subscript gives the number of rows and columns.', 'M');
    if (symbol === 'd' && /\\mathbf\s*d/.test(tex || '')) return entry('the matrix-size sequence d',
      'The bold letter d names the [[sequence]] of matrix sizes. Its nth entry is written \\(d_n\\).', '\\mathbf d');
    if (NAMED_OBJECTS[symbol]) return NAMED_OBJECTS[symbol];
    if (/^[ndij][∏⊕⨁∩⋂]$/.test(symbol)) {
      var operation = symbol.slice(-1).replace('⨁', '⊕').replace('⋂', '∩');
      return entry('indexed ' + NOTATION[operation].name,
        'The small letter is an [[index]] telling which family is used. ' +
        NOTATION[operation].explanation, NOTATION[operation].tex);
    }
    if (symbol.endsWith('⋂')) {
      return entry('intersection over the written choices',
        'The large intersection sign means the condition must hold for every choice written beneath it. ' +
        'The arrow inside the label describes a [[homomorphism]].', '\\bigcap');
    }
    if (/^d?n$/.test(symbol)) return entry('the indexed size d n',
      'The subscript n is an [[index]]. The symbol \\(d_n\\) is the number of rows and columns used at stage n.', 'd_n');
    if (/^x?n$/.test(symbol)) return entry('the nth sequence entry',
      'The subscript n is an [[index]]. The symbol \\(x_n\\) is the matrix in position n of the [[sequence]].', 'x_n');
    if (symbol === '{(') return entry('the start of set-builder notation',
      'The brace begins a [[set]] description, and the parenthesis begins the notation for a [[sequence]].', '\\{(');
    if (symbol === '∥') return entry('operator-norm bars',
      'The double bars ask for the [[operator norm]] of the matrix written between them.', '\\lVert x\\rVert');
    if (/^(uL|τL)$/.test(symbol)) {
      return entry('the beginning of a conjugated subgroup',
        'Letters written side by side are multiplied. Together with the following inverse, this applies [[conjugation]] to the [[subgroup]] L.', symbol === 'uL' ? 'uL' : '\\tau L');
    }
    if (/^(u|τ|f|πQ)−1$/.test(symbol)) {
      var base = symbol.slice(0, -2);
      return entry('inverse notation',
        'The superscript −1 means [[inverse]]. For a [[function]] such as f or pi, the surrounding set notation uses it to mean [[preimage]].',
        (base === 'τ' ? '\\tau' : base === 'πQ' ? '\\pi_Q' : base) + '^{-1}');
    }
    if (symbol === '−1') return entry('inverse exponent',
      'A superscript −1 means [[inverse]]: the operation that undoes the named group element, matrix, or map.', '^{-1}');
    if (symbol === 'RadMF' || symbol === 'Rad' || symbol === 'MF') return entry('the MF-radical label',
      'These letters are parts of the symbol for the [[MF radical]]. MF names the approximation rule and Rad abbreviates radical.', '\\operatorname{Rad}_{\\mathrm{MF}}');
    if (symbol === 'ker') return entry('kernel abbreviation',
      'The letters ker abbreviate [[kernel]]: all inputs that the following map sends to the [[identity]].', '\\ker');
    if (symbol === 'isMF') return entry('is an MF group',
      'The preceding [[quotient group]] satisfies the definition of an [[MF group]].', '\\text{is MF}');
    if (symbol === 'and') return entry('logical and',
      'Both the condition before this word and the condition after it must be true.', '\\text{and}');
    if (symbol === 'Mdn') return entry('the matrix set at stage n',
      'This is the [[set]] of square [[matrix|matrices]] with \\(d_n\\) rows and columns and [[complex number|complex-number]] entries.', 'M_{d_n}(\\mathbb C)');
    if (symbol === 'Qd') return entry('the chosen norm matrix corona',
      'The calligraphic Q names a [[norm matrix corona]], and the subscript d records its [[sequence]] of matrix sizes.', '\\mathcal Q_{\\mathbf d}');
    if (symbol === 'U') return entry('the unitary-elements symbol U',
      'U selects the [[unitary matrix|unitary elements]] inside the surrounding matrix object.', '\\mathcal U');
    if (/^π:G→U\(Qd\)$/.test(symbol)) return entry('a representation pi from G',
      'The Greek letter pi names a [[homomorphism]] from the [[group]] G to the unitary elements of the [[norm matrix corona]].', '\\pi\\colon G\\to\\mathcal U(\\mathcal Q_{\\mathbf d})');
    if (symbol === 'Comp' || symbol === 'CompG') return entry('the compression-set label',
      'Comp abbreviates the [[set]] of group elements whose [[conjugation]] sends L back inside L. A subscript G names the surrounding [[group]].', '\\operatorname{Comp}_G');
    if (symbol === 'D') return entry('the compression-defect label',
      'The decorated D is the chosen name for the [[normal closure]] of the compression [[commutator|commutators]].', '\\mathfrak D');
    if (symbol === 'CG') return entry('the centralizer in G',
      'This is the [[centralizer]] of L computed inside the [[group]] G.', 'C_G');
    if (symbol === '⟨' || symbol === '⟩') return entry('normal-closure bracket',
      'The doubled angle brackets enclose generators of a [[normal closure]]. A following subscript names the surrounding group.', '\\langle\\!\\langle d\\rangle\\!\\rangle');
    if (symbol === 'F') return entry('the field symbol F',
      'The blackboard-style F names a [[field]]. The following subscript tells which field.', '\\mathbb F');
    if (symbol === 'EL') return entry('the elementary-group label EL',
      'EL names an [[elementary group]]. Its subscript gives the matrix size and its parenthesized input gives the entry [[ring]].', '\\operatorname{EL}');
    if (symbol === 'e') return entry('the elementary-matrix letter e',
      'The letter e names an [[elementary matrix]]. Its subscript gives a row and column.', 'e');
    if (symbol === 'E') return entry('the matrix-unit letter E',
      'The capital E names a [[matrix]] with one nonzero entry. Its subscript gives the row and column.', 'E');
    if (symbol === 'ij' || /^[0-9]{2}$/.test(symbol)) return entry('row and column indices',
      'The two subscript symbols name a matrix row followed by a matrix column.', symbol);
    if (symbol === 's' || symbol === 't') return entry('a Leavitt-generator letter',
      'The letter, together with its subscript 0 or 1, names one of the four generators of the [[Leavitt algebra]].', symbol);
    if (/^(?:ti|sj|s[01]|t[01])$/.test(symbol)) return entry('an indexed Leavitt-algebra generator',
      'The letter s or t names a generator of the [[Leavitt algebra]]. Its subscript is an [[index]] selecting 0, 1, i, or j; it is not a power.', symbol[0] + '_{' + symbol.slice(1) + '}');
    if (symbol === 'δ' || symbol === 'δij') return entry('the Kronecker delta',
      'The [[Kronecker delta]] \\(\\delta_{ij}\\) is 1 when i equals j and 0 otherwise.', '\\delta_{ij}');
    if (symbol === '1.') return entry('identity followed by punctuation',
      'The 1 is the [[identity]]. The period ends the mathematical sentence.', '1.');
    if (symbol === 'W') return entry('the group letter W',
      'W names the constructed [[group]]. Its subscript Q records which chosen group Q was used.', 'W');
    if (/^Eij$/.test(symbol)) return entry('the matrix unit E i j',
      'This [[matrix]] has a single 1 in row i, column j and 0 in every other position. The letters i and j are [[index|indices]].', 'E_{ij}');
    if (/^e[0-9ij]+$/.test(symbol)) return entry('an elementary-matrix symbol',
      'The letter e names an [[elementary matrix]]. Its subscript gives the row and column [[index|indices]] of the extra entry.', 'e_{ij}');
    if (/^WQ$/.test(symbol)) return entry('the group W sub Q',
      'This is the [[group]] W built from the chosen group Q. The small Q is a subscript naming that choice.', 'W_Q');
    if (/^πQ$/.test(symbol)) return entry('the map pi sub Q',
      'This [[homomorphism]] sends the group \\(W_Q\\) onto Q. The subscript Q names its destination.', '\\pi_Q');
    if (/^CH$/.test(symbol)) return entry('the centralizer in H',
      'This is the [[centralizer]] computed inside the [[group]] H.', 'C_H');
    if (/^clMFG$/.test(symbol)) return entry('MF closure inside G',
      'This symbol names the MF [[closure operation]] performed inside the [[group]] G.', '\\operatorname{cl}_{\\mathrm{MF}}^G');
    if (symbol === 'cl' || symbol === 'clMFQ') return entry('MF-closure label',
      'The letters cl abbreviate the MF [[closure operation]]. A superscript names the surrounding [[group]].', '\\operatorname{cl}_{\\mathrm{MF}}');
    if (symbol === '))') return entry('two closing parentheses',
      'The inner parenthesis ends the input to the MF-closure rule. The outer parenthesis ends the input to the preimage function.', '))');
    if (/^[0-9]+$/.test(symbol)) {
      return entry('the number ' + symbol,
        symbol + ' is an ordinary whole number used as a size, count, row, column, or index.', symbol);
    }
    return null;
  }

  function texOf(math) {
    var annotation = math && math.querySelector('annotation[encoding="application/x-tex"]');
    return annotation ? annotation.textContent : '';
  }

  function explainTerm(term) {
    return TERMS[clean(term)] || null;
  }

  function renderTex(node, tex) {
    if (!window.katex || typeof window.katex.renderToString !== 'function') {
      throw new Error('KaTeX is required for mathematical explanations');
    }
    node.innerHTML = window.katex.renderToString(tex, {
      macros: window.CAIRN_MATH_MACROS || {},
      displayMode: false,
      throwOnError: false,
      strict: false,
      trust: false
    });
  }

  var TERM_NAMES = Object.keys(TERMS).sort(function (left, right) {
    return right.length - left.length;
  });

  function termForms(term) {
    var plural;
    if (term === 'matrix') plural = 'matrices';
    else if (/[^aeiou]y$/.test(term)) plural = term.slice(0, -1) + 'ies';
    else if (/(?:s|x|ch|sh)$/.test(term)) plural = term + 'es';
    else plural = term + 's';
    return plural === term ? [term] : [term, plural];
  }

  function termAt(text, offset, excludedTerm) {
    var lower = text.toLowerCase();
    for (var i = 0; i < TERM_NAMES.length; i++) {
      var term = TERM_NAMES[i];
      if (term === excludedTerm) continue;
      var forms = termForms(term);
      for (var j = 0; j < forms.length; j++) {
        var form = forms[j];
        if (lower.slice(offset, offset + form.length) !== form.toLowerCase()) continue;
        var before = offset ? text[offset - 1] : '';
        var after = text[offset + form.length] || '';
        if (/[A-Za-z0-9]/.test(before) || /[A-Za-z0-9]/.test(after)) continue;
        return { term: term, length: form.length };
      }
    }
    return null;
  }

  function appendLinkedPlainText(node, value, excludedTerm) {
    var text = String(value || '');
    var plainStart = 0;
    var cursor = 0;
    while (cursor < text.length) {
      var match = termAt(text, cursor, excludedTerm);
      if (!match) { cursor++; continue; }
      if (cursor > plainStart) node.appendChild(document.createTextNode(text.slice(plainStart, cursor)));
      var button = document.createElement('button');
      button.type = 'button';
      button.className = 'math-term-help';
      button.setAttribute('data-term', match.term);
      button.textContent = text.slice(cursor, cursor + match.length);
      node.appendChild(button);
      cursor += match.length;
      plainStart = cursor;
    }
    if (plainStart < text.length) node.appendChild(document.createTextNode(text.slice(plainStart)));
  }

  function setLinkedText(node, value, excludedTerm) {
    node.textContent = '';
    var text = String(value || '');
    var cursor = 0;
    var pattern = /\[\[([^|\]]+)(?:\|([^\]]+))?\]\]|\\\(([\s\S]*?)\\\)/g;
    var match;
    while ((match = pattern.exec(text))) {
      if (match.index > cursor) appendLinkedPlainText(node, text.slice(cursor, match.index), excludedTerm);
      if (match[3] != null) {
        var math = document.createElement('span');
        math.className = 'math-explainer-inline-math';
        renderTex(math, match[3]);
        node.appendChild(math);
      } else {
        var canonical = clean(match[1]);
        var label = clean(match[2] || match[1]);
        if (!TERMS[canonical] || canonical === excludedTerm) {
          appendLinkedPlainText(node, label, excludedTerm);
        } else {
          var button = document.createElement('button');
          button.type = 'button';
          button.className = 'math-term-help';
          button.setAttribute('data-term', canonical);
          button.textContent = label;
          node.appendChild(button);
        }
      }
      cursor = pattern.lastIndex;
    }
    if (cursor < text.length) appendLinkedPlainText(node, text.slice(cursor), excludedTerm);
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
    var symbol = box.querySelector('.math-explainer-symbol');
    symbol.textContent = '';
    if (state.info.tex) renderTex(symbol, state.info.tex);
    else symbol.textContent = state.symbol;
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
      node.classList.contains('mbin') || node.classList.contains('mrel') ||
      node.classList.contains('mopen') || node.classList.contains('mclose') ||
      node.classList.contains('mpunct');
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
      var formulaInfo = group[0];
      math.__mathExplanation = entry(
        'How to read this formula: ' + formulaInfo.name,
        formulaInfo.explanation,
        tex);
      math.classList.add('math-formula-help');
      math.setAttribute('tabindex', '0');
      math.setAttribute('role', 'button');
      math.setAttribute('aria-label', 'Explain the complete formula');
      math.setAttribute('title', 'Explain the complete formula');
      var nodes = visual.querySelectorAll('.mord, .mop, .mbin, .mrel, .mopen, .mclose, .mpunct');
      for (var j = 0; j < nodes.length; j++) {
        var node = nodes[j];
        if (!isTopLevelMathObject(node)) continue;
        var info = sourceExplanation(clean(node.textContent), tex, group) ||
            notationExplanation(clean(node.textContent), tex);
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

  function addPrompt() {
    if (document.querySelector('.math-help-prompt')) return;
    var anchor = document.querySelector('.paper-key, .paper-head, nav.top, header');
    if (!anchor || !document.querySelector('.math-symbol-help')) return;
    var prompt = document.createElement('p');
    prompt.className = 'math-help-prompt';
    prompt.textContent = 'Click highlighted math, then follow underlined terms.';
    anchor.insertAdjacentElement('afterend', prompt);
  }

  document.addEventListener('click', function (event) {
    var term = event.target.closest && event.target.closest('.math-term-help');
    if (term) {
      event.preventDefault(); event.stopPropagation();
      openTerm(term.getAttribute('data-term')); return;
    }
    if (event.target.closest && event.target.closest('.math-explainer')) return;
    var object = event.target.closest && event.target.closest('.math-symbol-help, .math-formula-help');
    var math = object && (object.classList.contains('katex') ? object : object.closest('.katex'));
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
        event.target.classList && (event.target.classList.contains('math-symbol-help') ||
        event.target.classList.contains('math-formula-help'))) {
      var math = event.target.classList.contains('katex') ? event.target : event.target.closest('.katex');
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
    notationExplanation: notationExplanation,
    explainTerm: explainTerm,
    renderTex: renderTex,
    decorate: decorate
  };
}());
