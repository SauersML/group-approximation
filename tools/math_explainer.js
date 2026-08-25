(function () {
  'use strict';

  if (window.__cairnMathExplainerInstalled) return;
  window.__cairnMathExplainerInstalled = true;

  var panel;
  var lastObject;
  var history = [];
  var current;
  var pinned = false;

  /* Words inside an explanation may be followed to these short definitions.
     TeX declarations supply contextual explanations; the notation table below
     supplies fixed meanings for standard symbols in those declared formulas. */
  var TERMS = {
    'set': entry('set',
      'A collection of objects. An object either belongs to the set or it does not.'),
    'element': entry('element',
      'One object belonging to a [[set]]. For example, each individual move in a [[group]] is an element of that group.'),
    'sequence': entry('sequence',
      'A list in a fixed order: first, second, third, and so on. A [[subscript]] such as n names a position in the list.'),
    'index': entry('index',
      'A label that selects one position, [[row]], [[column]], or item. It is often written as a small [[subscript]] below a letter.'),
    'symbol': entry('symbol',
      'A written mark used as a mathematical name or instruction, such as G, +, or \\(\\le\\).'),
    'variable': entry('variable',
      'A letter or [[symbol]] used as a name whose value is specified by the surrounding sentence.'),
    'expression': entry('expression',
      'A piece of mathematical writing made from numbers, names, and operation [[symbol|symbols]], such as \\(a+bi\\). It need not make a claim by itself.'),
    'equation': entry('equation',
      'A statement with an equals sign saying that the [[expression|expressions]] on its two sides have the same value.'),
    'subscript': entry('subscript',
      'A small label written below and to the right of a [[symbol]]. It selects a version, position, row, column, or stage; it is not multiplication.'),
    'superscript': entry('superscript',
      'A small label written above and to the right of a [[symbol]]. It can mean a power, an [[inverse]], or another qualifier explained by context.'),
    'calligraphic letter': entry('calligraphic letter',
      'A letter drawn in a decorative script, such as \\(\\mathcal Q\\). The style distinguishes its mathematical role; it does not change the alphabetic letter.'),
    'blackboard-bold letter': entry('blackboard-bold letter',
      'A doubled-stroke letter such as \\(\\mathbb C\\) or \\(\\mathbb F\\), conventionally used to name familiar number systems.'),
    'bold letter': entry('bold letter',
      'A thickened letter such as \\(\\mathbf d\\). Here it names a whole [[sequence]] rather than one entry of that sequence.'),
    'fraktur letter': entry('fraktur letter',
      'A letter drawn in an ornate blackletter style, such as \\(\\mathfrak D\\). The style helps distinguish this object from an ordinary letter D.'),
    'Greek letter': entry('Greek letter',
      'A letter from the Greek alphabet used as a mathematical name. For example, \\(\\pi\\) is read “pi,” \\(\\tau\\) is “tau,” and \\(\\ell\\) is “ell.”'),
    'circled-plus sign': entry('circled-plus sign',
      'The symbol \\(\\bigoplus\\). Here it names the [[direct sum]], not ordinary addition.'),
    'function': entry('function',
      'A rule that assigns exactly one output to each allowed input. Its [[domain]] is the allowed-input [[set]], and this paper also calls a function a map.'),
    'map': entry('map',
      'Another word for a [[function]], especially when the inputs and outputs are mathematical objects.'),
    'domain': entry('domain',
      'The [[set]] of allowed inputs of a [[function]].'),
    'target': entry('target',
      'The [[set]] in which a [[function]] is required to place its outputs.'),
    'composition': entry('composition',
      'Performing one [[function]] and then feeding its output into a second function. The notation \\(h\\circ f\\) means do f first and h second.'),
    'precomposition': entry('precomposition',
      'Changing a [[function]] by doing another function before it. Precomposing h with f gives the [[composition]] \\(h\\circ f\\), whose rule is \\(x\\mapsto h(f(x))\\).'),
    'image': entry('image',
      'The output of a [[function]], or the [[set]] of outputs obtained from several inputs.'),
    'preimage': entry('preimage',
      'Given some outputs of a [[function]], their preimage is the [[set]] of all inputs that produce those outputs.'),
    'surjective': entry('surjective',
      'A [[function]] is surjective, or onto, when every possible output is reached by at least one input.'),
    'bijection': entry('bijection',
      'A perfect pairing between two [[set|sets]]: every object on either side is paired with exactly one object on the other side.'),
    'isomorphism': entry('isomorphism',
      'A reversible [[homomorphism]]: a pairing that preserves multiplication and can be undone. It shows that two [[group|groups]] have the same multiplication pattern even when their elements have different names.'),
    'embedding': entry('embedding',
      'A [[faithful]] [[homomorphism]] that places one mathematical object inside another without merging any two of its elements.'),
    'intersection': entry('intersection',
      'The objects shared by every [[set]] being considered.'),
    'infinite product': entry('infinite product',
      'A [[set]] of [[sequence|sequences]] made by choosing one entry from each set in an endless list of sets.'),
    'direct sum': entry('direct sum',
      'In this paper, the [[sequence|sequences]] of matrices whose [[operator norm|operator norms]] have [[limit]] zero. These eventually negligible errors form the [[c0-direct sum]].'),
    'quotient': entry('quotient',
      'A construction that declares selected differences to count as zero. Objects that differ only by one of those ignored differences are then treated as equal.'),
    'set-builder notation': entry('set-builder notation',
      'A way to describe a [[set]] using braces. The part before the colon names possible elements; the part after the colon gives the rule they must satisfy.'),
    'bounded sequence': entry('bounded sequence',
      'A [[sequence]] whose entries never grow past one fixed size. Equivalently, its entries are [[uniformly bounded]] by one common number.'),
    'uniformly bounded': entry('uniformly bounded',
      'Controlled by one fixed upper bound that works for every entry in a [[sequence]]. The bound does not change with the [[index]].'),
    'subsequence': entry('subsequence',
      'A new [[sequence]] formed by keeping selected entries of the original sequence in their original order, possibly skipping infinitely many others.'),
    'limit': entry('limit',
      'The value that a changing quantity approaches. Saying a sequence tends to zero means its entries can be made as small as desired by going far enough along the sequence.'),
    'limsup': entry('limsup',
      'Short for “limit superior.” For a [[sequence]], it is the largest value that the entries keep coming close to infinitely often, even when the sequence has no single [[limit]].'),
    'lower bound': entry('lower bound',
      'A number that a quantity is guaranteed not to go below. A positive lower bound keeps the quantity a definite distance above zero.'),
    'subspace': entry('subspace',
      'A [[set]] of [[vector|vectors]] inside a [[vector space]] that includes zero and remains closed under vector addition and scalar multiplication.'),
    'asymptotic': entry('asymptotic',
      'Describing what happens farther and farther along a [[sequence]], while early entries are allowed to behave differently.'),
    'lift': entry('lift',
      'A representative chosen before forming a [[quotient]]. A lift of a corona element is an actual matrix [[sequence]] whose equivalence class is that element.'),
    'polar correction': entry('polar correction',
      'A procedure that replaces an almost-[[unitary matrix|unitary matrix]] by a nearby exactly unitary one, using the positive square root of \\(A^*A\\).'),
    'spectral rounding': entry('spectral rounding',
      'A procedure that replaces an almost-[[projection]] by a nearby exact projection: eigenvalues near 0 are changed to 0 and those near 1 are changed to 1.'),
    'free ultrafilter': entry('free ultrafilter',
      'A rule for declaring which subsets of the positive whole numbers count as “large,” agreeing with ordinary eventual behavior but selecting a limit for every bounded [[sequence]].'),
    'ultraproduct': entry('ultraproduct',
      'A construction that combines a [[sequence]] of mathematical objects into one limit object, treating two sequences as equal when they agree according to an ultrafilter.'),
    'Hilbert-space ultraproduct': entry('Hilbert-space ultraproduct',
      'An [[ultraproduct]] of [[Hilbert space|Hilbert spaces]]. Bounded vector sequences become vectors in one larger Hilbert space, with lengths computed by the ultrafilter limit.'),
    'modulo c0': entry('modulo c0',
      'Equal after ignoring an error [[sequence]] whose size has [[limit]] zero. In other words, equal inside the relevant [[norm matrix corona]].'),
    'corona class': entry('corona class',
      'The single element of a [[corona]] represented by a matrix [[sequence]]. Sequences differing by an error that tends to zero have the same corona class.'),
    'universal Hilbert–Schmidt kernel': entry('universal Hilbert–Schmidt kernel',
      'The [[normal subgroup]] of elements that every operator-norm [[asymptotic representation]] sends toward the [[identity]] in normalized [[Hilbert–Schmidt norm]].'),
    'approximation': entry('approximation',
      'A simpler or finite substitute that is not perfectly exact but can be made as close to exact as required.'),
    'model': entry('model',
      'A concrete object used to imitate the behavior of another object. Here the concrete objects are finite [[matrix|matrices]] that imitate group multiplication.'),
    'finite-matrix model': entry('finite-matrix model',
      'A [[model]] that assigns a finite square [[matrix]] to each relevant [[group]] element, arranged so that multiplying matrices almost matches multiplying group elements.'),
    'multiplication error': entry('multiplication error',
      'The difference between the matrix obtained by multiplying two assigned matrices and the matrix assigned to the corresponding product in the [[group]].'),
    'unitarity error': entry('unitarity error',
      'The amount by which a matrix fails to be [[unitary matrix|unitary]], measured by how far \\(A^*A\\) and \\(AA^*\\) are from the [[identity matrix]].'),
    'asymptotic representation': entry('asymptotic representation',
      'A [[sequence]] of finite-matrix [[model|models]] whose [[multiplication error|multiplication errors]] approach zero. It becomes more accurate at later stages, though no one finite stage must be exact.'),
    'asymptotic commutant': entry('asymptotic commutant',
      'A [[set]] of bounded matrix [[sequence|sequences]] that increasingly commute with a specified family: the chosen norm of each [[commutator]] tends to zero, even though the matrices need not commute exactly at any finite stage.'),
    'separate elements': entry('separate elements',
      'To send different [[element|elements]] to detectably different outputs. An approximation that separates elements does not accidentally make distinct group moves look identical.'),
    'permanence': entry('permanence',
      'A result saying that a property survives a construction. For example, an MF permanence theorem proves that building a new group in a specified way from MF groups produces another MF group.'),
    'non-approximability': entry('non-approximability',
      'The impossibility of modeling an object with the permitted finite [[approximation|approximations]] while making all required errors approach zero.'),
    'Schatten norm': entry('Schatten norm',
      'A family of matrix-size measurements built from the singular values of a matrix. The Hilbert–Schmidt norm is the Schatten 2-norm; operator norm is the limiting infinity-norm case.'),
    'soficity': entry('soficity',
      'The property that a [[group]] can be approximated by finite permutations with error measured by the fraction of points on which two permutations disagree.'),
    'hyperlinearity': entry('hyperlinearity',
      'The property that a [[group]] can be approximated by finite [[unitary matrix|unitary matrices]] with error measured in normalized [[Hilbert–Schmidt norm]].'),
    'semidirect product': entry('semidirect product',
      'A [[group]] built from two groups when one is allowed to act on the other. It resembles a [[direct product]], but multiplication can twist one coordinate.'),
    'double of a group': entry('double of a group',
      'Two copies of the same [[group]] joined along matching copies of a shared [[subgroup]], producing a special [[amalgamated free product]].'),
    'stability': entry('stability',
      'The property that an almost-solution of specified equations must lie near an exact solution. The chosen way of measuring error is part of the definition.'),
    'coordinatewise': entry('coordinatewise',
      'Performed separately at each position of a [[sequence]]. Coordinatewise conjugation applies the same conjugation rule within every matrix stage.'),
    'countable': entry('countable',
      'Able to be placed in a [[sequence]], so the elements can be listed first, second, third, and so on. A finite [[set]] is countable too.'),
    'finite-dimensional': entry('finite-dimensional',
      'Described using a fixed finite number of independent [[coordinate|coordinates]]. For example, ordinary 3-dimensional space needs three coordinates.'),
    'infinite-dimensional': entry('infinite-dimensional',
      'Requiring infinitely many independent [[coordinate|coordinates]] rather than any fixed finite list. This allows behavior impossible in finite-dimensional spaces.'),
    'group': entry('group',
      'A [[set]] with a rule for combining any two elements. The result stays in the set; regrouping three elements does not change the result; there is an [[identity]] element that changes nothing; and every element has an [[inverse]]. Group elements can represent symmetries or actions, but they do not have to.'),
    'commute': entry('commute',
      'Two moves commute when doing the first and then the second gives the same result as doing them in the opposite order.'),
    'nontrivial': entry('nontrivial',
      'Not reduced to only the do-nothing case. A nontrivial [[group]] contains at least one element besides the [[identity]].'),
    'nonzero': entry('nonzero',
      'Different from zero. A nonzero number, [[vector]], or [[matrix]] has at least one part that is not zero.'),
    'nonidentity': entry('nonidentity',
      'Different from the [[identity]], so it is not the do-nothing group element or matrix.'),
    'trivial': entry('trivial',
      'Containing no information beyond the do-nothing case. A trivial [[group]] has only its [[identity]], while a trivial map sends everything to one value.'),
    'rigidity': entry('rigidity',
      'A condition saying that approximate behavior is forced to come from exact behavior; small errors cannot create genuinely new possibilities.'),
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
    'endomorphism': entry('endomorphism',
      'A [[homomorphism]] or other structure-preserving [[function]] whose [[domain]] and [[target]] are the same object.'),
    'injective': entry('injective',
      'A [[function]] that never sends two different inputs to the same output. It therefore preserves the ability to distinguish its inputs.'),
    'representation': entry('representation',
      'A [[homomorphism]] that assigns a concrete [[matrix]] or [[operator]] to every [[group]] element, so combining group elements matches combining their assigned actions.'),
    'faithful': entry('faithful',
      'A [[homomorphism]] is faithful when different inputs always have different outputs, so it loses no information.'),
    'linear representation': entry('linear representation',
      'A [[representation]] by invertible matrices acting on a [[vector space]]. Group multiplication must match matrix multiplication exactly.'),
    'nondegenerate representation': entry('nondegenerate representation',
      'A representation of an operator algebra that acts on the whole [[Hilbert space]]: no nonzero vector is ignored by every represented operator.'),
    'trivial homomorphism': entry('trivial homomorphism',
      'A [[homomorphism]] that sends every input to the [[identity]], so its output carries no information about the input.'),
    'kernel': entry('kernel',
      'All inputs that a [[homomorphism]] sends to the [[identity]]. A large kernel means the map forgets many elements.'),
    'quotient group': entry('quotient group',
      'The [[group]] obtained by treating every element of a chosen [[normal subgroup]] as the [[identity]].'),
    'group of integers': entry('group of integers',
      'The whole numbers \\(\ldots,-2,-1,0,1,2,\ldots\\) viewed as a [[group]] under addition. Its [[identity]] is 0, and the [[inverse]] of an integer is its negative.'),
    'cyclic subgroup': entry('cyclic subgroup',
      'A [[subgroup]] made from one element by repeatedly combining that element and its [[inverse]].'),
    'normal closure': entry('normal closure',
      'The smallest [[normal subgroup]] containing the listed elements. The notation \\(\\langle\\!\\langle d\\rangle\\!\\rangle_G\\) means the normal closure of d inside G.'),
    'normal generation': entry('normal generation',
      'An element or [[subgroup]] normally generates G when its [[normal closure]] is all of G. Conjugating and combining it then produces every element of G.'),
    'fully invariant': entry('fully invariant',
      'A [[subgroup]] is fully invariant when every [[endomorphism]] of the surrounding group sends it back inside itself.'),
    'centralizer': entry('centralizer',
      'The [[subgroup]] of elements that commute with a chosen set: doing either move first gives the same result.'),
    'center': entry('center',
      'All elements that [[commute]] with every other element of the surrounding [[group]], [[ring]], or [[algebra]].'),
    'commutator': entry('commutator',
      'For elements a and b, \\([a,b]=aba^{-1}b^{-1}\\). It equals the [[identity]] exactly when doing a then b gives the same result as doing b then a.'),
    'compression': entry('compression',
      'Restricting an action to a smaller part, or sending a [[subgroup]] into a copy contained inside itself. “One-sided” means containment is required without equality.'),
    'simple group': entry('simple group',
      'A nontrivial [[group]] whose only [[normal subgroup|normal subgroups]] are the identity alone and the whole group.'),
    'simple ring': entry('simple ring',
      'A nonzero [[ring]] with no proper nonzero two-sided ideals. Informally, no nonzero part closed under multiplication from both sides can remain smaller than the whole ring.'),
    'residually finite': entry('residually finite',
      'A [[group]] in which every [[nonidentity]] element stays nonidentity in at least one [[homomorphism]] to a finite group. Finite tests can therefore detect every element.'),
    'permutation representation': entry('permutation representation',
      'A [[representation]] in which each group element rearranges a finite [[set]]. Families of these representations can show that a group is [[residually finite]].'),
    'amenable': entry('amenable',
      'A technical averaging property of a [[group]]. Finite and commutative groups are examples; the paper uses the fact that an amenable group cannot contain an infinite property-(T) subgroup.'),
    'matrix': entry('matrix',
      'A rectangular table of entries arranged in horizontal [[row|rows]] and vertical [[column|columns]]. An entry may be an ordinary number or an element of a [[ring]].'),
    'row': entry('row',
      'A horizontal line of entries in a [[matrix]].'),
    'column': entry('column',
      'A vertical line of entries in a [[matrix]], read from top to bottom.'),
    'coordinate': entry('coordinate',
      'One numbered position in a list or [[vector]]. In an [[ordered pair]] \\((q,a)\\), q is the first coordinate and a is the second.'),
    'ordered pair': entry('ordered pair',
      'Two objects written as \\((q,a)\\), where position matters: q is the first [[coordinate]] and a is the second.'),
    'diagonal': entry('diagonal',
      'The positions in a square [[matrix]] where the row number equals the column number.'),
    'off-diagonal': entry('off-diagonal',
      'A position in a square [[matrix]] where the row number and column number are different.'),
    'invertible': entry('invertible',
      'Able to be undone. An invertible [[matrix]] has another matrix that multiplies with it to give the [[identity matrix]].'),
    'transpose': entry('transpose',
      'The [[matrix]] obtained by exchanging rows with columns.'),
    'complex conjugate': entry('complex conjugate',
      'For \\(a+bi\\), change the sign of the imaginary part to obtain \\(a-bi\\).'),
    'identity matrix': entry('identity matrix',
      'A square [[matrix]] with 1 on its main [[diagonal]] and 0 everywhere else. Multiplying by it changes nothing.'),
    'real number': entry('real number',
      'A number represented by a point on the ordinary number line, including whole numbers, fractions, and irrational numbers such as \\(\\sqrt2\\).'),
    'complex number': entry('complex number',
      'A number of the form \\(a+bi\\), where a and b are [[real number|real numbers]] and the new number i satisfies \\(i^2=-1\\).'),
    'vector space': entry('vector space',
      'A collection of [[vector|vectors]] that can be added and multiplied by [[scalar|scalars]] while staying in the collection.'),
    'vector': entry('vector',
      'An ordered list of [[coordinate|coordinates]], often pictured as an arrow. [[matrix|Matrices]] act on vectors by combining their coordinates.'),
    'operator': entry('operator',
      'A [[function]] that takes a [[vector]] as input and returns a vector as output.'),
    'operator norm': entry('operator norm',
      'The largest stretch factor of a [[matrix]] or [[operator]]. A small operator norm means every input vector is changed by only a small amount.'),
    'Hilbert–Schmidt norm': entry('Hilbert–Schmidt norm',
      'A size for a [[matrix]] obtained from the square root of the sum of the squared entry sizes. The [[normalized Hilbert–Schmidt norm|normalized version]] rescales matrices of different dimensions for fair comparison.'),
    'normalized Hilbert–Schmidt norm': entry('normalized Hilbert–Schmidt norm',
      'The [[Hilbert–Schmidt norm]] scaled by matrix size. Unlike [[operator norm]], it measures average squared behavior rather than the single most-stretched direction.'),
    'trace': entry('trace',
      'The sum of the entries on the main [[diagonal]] of a square [[matrix]]. It also equals the sum of the matrix’s eigenvalues, counted with repetition.'),
    'normalized trace': entry('normalized trace',
      'The [[trace]] divided by the matrix dimension, so the [[identity matrix]] always has normalized trace 1 regardless of its size.'),
    'adjoint': entry('adjoint',
      'For a complex [[matrix]], transpose it and take the [[complex conjugate]] of every entry. The symbol \\(A^*\\) denotes the adjoint of A.'),
    'self-adjoint': entry('self-adjoint',
      'Equal to its own [[adjoint]], so \\(A^*=A\\). Self-adjoint matrices have real eigenvalues and play the role of real-valued quantities in operator theory.'),
    'projection': entry('projection',
      'A square [[matrix]] or [[operator]] satisfying \\(P^2=P\\) and \\(P^*=P\\). It keeps vectors in one chosen subspace and sends perpendicular directions to zero.'),
    'projection domination': entry('projection domination',
      'A projection P is dominated by Q, written \\(P\\le Q\\), when every direction kept by P is also kept by Q. Equivalently, the [[range]] of P lies inside the range of Q.'),
    'fixed vector': entry('fixed vector',
      'A [[vector]] left unchanged by every specified group action. If the action is represented by matrices, v is fixed when every relevant matrix sends v to itself.'),
    'Kazhdan projection': entry('Kazhdan projection',
      'A special [[projection]] associated with a property-(T) [[group]], defined inside its [[maximal group C-star algebra]]. In any suitable [[representation]], it selects exactly the [[fixed vector|fixed vectors]].'),
    'maximal group C-star algebra': entry('maximal group C-star algebra',
      'A C-star algebra built from a [[group]] that packages all its [[unitary matrix|unitary]] representations at once. “Maximal” refers to using the largest compatible operator norm.'),
    'Kazhdan inequality': entry('Kazhdan inequality',
      'A quantitative form of property (T): when no nonzero vector is fixed, at least one chosen group element must move every vector by a definite amount.'),
    'Kazhdan set': entry('Kazhdan set',
      'A finite, usually [[symmetric set|symmetric]], set of group elements used to test property (T). Its [[Kazhdan constant]] measures how strong the test is: tiny movement by the set forces a nearby [[fixed vector]].'),
    'Kazhdan constant': entry('Kazhdan constant',
      'A positive number measuring the definite amount of movement guaranteed by a chosen [[Kazhdan set]] when no nonzero [[fixed vector]] exists.'),
    'symmetric set': entry('symmetric set',
      'A [[set]] of group elements that contains the [[inverse]] of each of its elements. Symmetry lets an argument use moves and their reverses on equal footing.'),
    'commutant': entry('commutant',
      'All [[operator|operators]] that [[commute]] with every operator in a chosen collection. It is the operator version of a [[centralizer]].'),
    'corner': entry('corner',
      'The smaller matrix or operator system \\(qAq\\) selected by a [[projection]] q. It keeps only the part acting on the directions preserved by q.'),
    'stably finite': entry('stably finite',
      'A finiteness condition for a [[ring]] or C-star algebra: even after passing to larger block matrices, a one-sided matrix inverse must also be a two-sided inverse.'),
    'unitarily equivalent': entry('unitarily equivalent',
      'Related by a change of orthonormal coordinates using a [[unitary matrix]]. Unitarily equivalent objects have the same geometric and spectral information.'),
    'matrix amplification': entry('matrix amplification',
      'Replacing each entry of an object by a block matrix, producing a larger matrix system. Stable finiteness requires the same finiteness rule at every such size.'),
    'Hilbert space': entry('Hilbert space',
      'A [[vector space]] with lengths and angles supplied by an [[inner product]], and with no missing limit points. It may have infinitely many independent directions.'),
    'inner product': entry('inner product',
      'A rule that measures lengths and angles between [[vector|vectors]]. The length of v is obtained from the square root of its inner product with itself.'),
    'orthogonal projection': entry('orthogonal projection',
      'A [[projection]] onto a subspace that removes the perpendicular component. It gives the closest vector lying in that subspace.'),
    'range': entry('range',
      'The [[set]] of outputs actually produced by a [[function]] or [[operator]]. For a projection, its range is the subspace it keeps.'),
    'operator inequality': entry('operator inequality',
      'A comparison such as \\(A\\ge B\\) meaning that \\(A-B\\) is positive: every vector gives a nonnegative value when tested against that difference.'),
    'positive element': entry('positive element',
      'A self-adjoint [[operator]] whose measured value on every vector is nonnegative. For a matrix, all its eigenvalues are nonnegative.'),
    'negative part': entry('negative part',
      'The portion of a self-adjoint [[operator]] coming from its negative eigenvalues. Its norm measures how far the operator is from being a [[positive element]].'),
    'unitary matrix': entry('unitary matrix',
      'An [[invertible]] square [[matrix]] over the [[complex number|complex numbers]] that preserves lengths and angles. Its [[inverse]] is obtained by taking the [[transpose]] and replacing every entry by its [[complex conjugate]].'),
    'unitary group': entry('unitary group',
      'The [[group]] consisting of all [[unitary matrix|unitary matrices]] of a fixed size, combined by matrix multiplication. In a [[norm matrix corona]], it similarly means all unitary elements of that object.'),
    'general linear group': entry('general linear group',
      'The [[group]] of all [[invertible]] square [[matrix|matrices]] of one fixed size over a chosen [[field]] or [[ring]]. It is commonly abbreviated GL.'),
    'ring': entry('ring',
      'A number-like system in which addition, subtraction, and multiplication are allowed. Unlike ordinary-number multiplication, its multiplication need not [[commute]].'),
    'unital': entry('unital',
      'Having a multiplicative [[identity]] 1. A unital [[ring]] or [[algebra]] includes an element that leaves every element unchanged when multiplied by it.'),
    'field': entry('field',
      'A number system in which addition, subtraction, multiplication, and division by [[nonzero]] numbers are allowed.'),
    'Kronecker delta': entry('Kronecker delta',
      'The symbol \\(\\delta_{ij}\\): it equals 1 when the [[index|indices]] i and j are equal, and 0 when they are different.'),
    'algebra': entry('algebra',
      'A [[ring]] whose elements can also be multiplied by numbers from a chosen [[field]].'),
    'C-star algebra': entry('C-star algebra',
      'An [[algebra]] of [[operator|operators]] over the [[complex number|complex numbers]], equipped with an [[adjoint]] and an [[operator norm]] that obey compatible rules. A structure-preserving map between them is a [[star-homomorphism]].'),
    'star-homomorphism': entry('star-homomorphism',
      'A [[homomorphism]] between C-star algebras that preserves addition, multiplication, the [[identity]], and the [[adjoint]] operation.'),
    'isometry': entry('isometry',
      'A [[function]] or [[operator]] that preserves lengths. In a C-star algebra, an element v is an isometry when \\(v^*v=1\\).'),
    'eigenvalue': entry('eigenvalue',
      'A number λ for which some nonzero [[vector]] v satisfies \\(Av=\\lambda v\\). Along that direction, the matrix A acts only by scaling.'),
    'singular value': entry('singular value',
      'A nonnegative number measuring how strongly a [[matrix]] stretches along one principal direction. The largest singular value is the [[operator norm]].'),
    'scalar': entry('scalar',
      'A number used to multiply every [[coordinate]] of a [[vector]] or every entry of a [[matrix]].'),
    'module': entry('module',
      'A [[vector space|vector-space-like]] object whose [[scalar|scalars]] come from a [[ring]] instead of necessarily coming from a [[field]].'),
    'free module': entry('free module',
      'A [[module]] with independent coordinate directions, analogous to ordinary coordinate space.'),
    'module rank': entry('module rank',
      'The number of independent coordinate directions in a [[free module]]. Leavitt’s example is unusual because one free module can be isomorphic to two copies of itself.'),
    'finitely generated': entry('finitely generated',
      'Built from a finite list of [[generator|generators]] using the allowed operations. The whole object may still contain infinitely many elements.'),
    'associative ring': entry('associative ring',
      'A [[ring]] whose multiplication satisfies \\((ab)c=a(bc)\\). Parentheses can therefore be moved without changing a product’s value.'),
    'purely infinite simple': entry('purely infinite simple',
      'A strong property of certain [[ring|rings]]: the ring is a [[simple ring]] and every nonzero part is large enough to reproduce the whole ring.'),
    'exchange ring': entry('exchange ring',
      'A [[ring]] in which approximate decompositions by [[projection|projection-like elements]] can be adjusted to exact ones. The paper uses a theorem known for this class of rings.'),
    'base field': entry('base field',
      'The chosen [[field]] whose numbers act as [[scalar|scalars]] in an [[algebra]]. For the binary Leavitt algebra here, the base field is \\(\\mathbb F_2\\).'),
    'central unit': entry('central unit',
      'An [[invertible]] element of a [[ring]] that also lies in its [[center]], so it [[commute|commutes]] with every ring element.'),
    'matrix unit': entry('matrix unit',
      'A [[matrix]] written \\(E_{ij}\\) with a single 1 in [[row]] i and [[column]] j and 0 everywhere else.'),
    'elementary root': entry('elementary root',
      'Another name here for a nonidentity [[elementary matrix]] \\(e_{ij}(a)\\). “Root” refers to its position in the elementary group, not to taking a square root.'),
    'block matrix': entry('block matrix',
      'A large [[matrix]] divided into rectangular smaller matrices called blocks. Ordinary matrix addition and multiplication are then performed block by block.'),
    'block diagonal': entry('block diagonal',
      'A [[block matrix]] whose off-diagonal blocks are zero. The notation \\(\\operatorname{diag}(A,I)\\) places A and I along its diagonal.'),
    'block-unipotent': entry('block-unipotent',
      'A [[block matrix]] with identity blocks on its main diagonal and a possibly nonzero block on just one side of that diagonal.'),
    'Whitehead factorization': entry('Whitehead factorization',
      'The displayed product that rewrites a [[block diagonal]] matrix as several [[block-unipotent]] matrices, which can then be built from [[elementary matrix|elementary matrices]].'),
    'coefficient': entry('coefficient',
      'A number or ring element multiplying a named term. In a [[matrix]], it can mean the entry occupying a specified row and column.'),
    'square-zero': entry('square-zero',
      'An element v satisfying \\(v^2=0\\) even though v itself may be [[nonzero]]. Multiplying it by itself makes it vanish.'),
    'root extraction': entry('root extraction',
      'The argument that starts from a complicated nonidentity matrix and, using [[commutator|commutators]], produces a nonzero [[elementary root]].'),
    'generated by relations': entry('generated by relations',
      'Start with named [[generator|generators]] and allow every expression made from them, while requiring the listed [[relation|relations]] to be true.'),
    'generator': entry('generator',
      'One of a chosen collection of building blocks from which every other element can be formed using the allowed operations.'),
    'relation': entry('relation',
      'An [[equation]] that the chosen [[generator|generators]] are required to satisfy.'),
    'elementary matrix': entry('elementary matrix',
      'An [[identity matrix]] with one additional entry away from the main diagonal.'),
    'elementary group': entry('elementary group',
      'The [[group]] formed by multiplying [[elementary matrix|elementary matrices]] of a fixed size. It is a subgroup of the corresponding [[general linear group]].'),
    'property (T)': entry('property (T)',
      'A [[rigidity]] feature of a [[group]]. Roughly, if the group moves some [[vector|vectors]] only a tiny amount, then some [[nonzero]] vector must be left completely fixed.'),
    'corona': entry('corona',
      'A conventional name here for a [[quotient]] of [[sequence|sequences]] that keeps their long-run behavior but treats two sequences as equal [[modulo c0|when their difference tends to zero]].'),
    'norm matrix corona': entry('norm matrix corona',
      'A [[corona]] made from [[bounded sequence|bounded sequences]] of finite [[matrix|matrices]]. Two sequences count as the same when the [[operator norm]] of their difference has [[limit]] zero.'),
    'corona norm': entry('corona norm',
      'The size of an element in a [[norm matrix corona]]. For a representing matrix [[sequence]], it is the limiting upper size measured by [[operator norm]], unchanged by errors tending to zero.'),
    'c0-direct sum': entry('c0-direct sum',
      'The [[direct sum]] of matrix [[sequence|sequences]] whose [[operator norm|operator norms]] approach zero. The “c-zero” label is the conventional name for sequences that vanish in the long run.'),
    'MF': entry('MF',
      'MF stands for “matricial field,” the historical name for this finite-matrix [[approximation]] property. A countable [[group]] is MF when its elements can be assigned finite-dimensional [[unitary matrix|unitary matrices]] at successive stages so that every [[multiplication error]] tends to zero in [[operator norm]], while each [[nonidentity]] element stays a positive operator-norm distance from the [[identity]] along infinitely many stages. Equivalently, the group embeds in the unitary group of a [[norm matrix corona]].'),
    'MF group': entry('MF group',
      'A [[group]] that has a [[faithful]] [[representation]] by sequences of finite [[unitary matrix|unitary matrices]] in a [[norm matrix corona]]. Equivalently, its [[multiplication error|multiplication errors]] approach zero in [[operator norm]] without merging distinct group elements.'),
    'MF radical': entry('MF radical',
      'The [[normal subgroup]] of elements sent to the [[identity]] by every [[homomorphism]] from the group into every [[norm matrix corona]]. This subgroup is [[fully invariant]].'),
    'radical': entry('radical',
      'In this paper, the [[normal subgroup]] containing exactly the elements that every allowed target [[homomorphism]] sends to the [[identity]].'),
    'Leavitt algebra': entry('Leavitt algebra',
      'A particular [[algebra]] built from four named elements \\(s_0,s_1,t_0,t_1\\) and two families of equations. Those equations let one [[free module]] behave like two copies of itself.'),
    'direct product': entry('direct product',
      'The [[group]] of [[ordered pair|ordered pairs]] \\((q,a)\\), with the first [[coordinate|coordinates]] combined together and the second coordinates combined together.'),
    'amalgamated free product': entry('amalgamated free product',
      'A [[group]] made by joining two groups along copies of a shared [[subgroup]], without adding [[relation|relations]] beyond those already present and the equations identifying the two copies. Its elements have an alternating [[normal form]].'),
    'factors through': entry('factors through',
      'A [[function]] factors through another [[map]] when it can be performed as a [[composition]] of two maps. The middle output retains everything the final function needs.'),
    'closure operation': entry('closure operation',
      'A rule that enlarges a [[set]] by adding everything forced by a chosen condition, and adds nothing further when applied a second time.'),
    'MF closure': entry('MF closure',
      'The [[closure operation]] that adds every group element all [[homomorphism|homomorphisms]] to [[MF group|MF groups]] must erase once they erase the chosen [[normal subgroup]].'),
    'pullback': entry('pullback',
      'Here, the [[preimage]] of a subgroup under a [[homomorphism]]: collect every input whose output lies in that subgroup.'),
    'functoriality': entry('functoriality',
      'The statement that a construction behaves predictably under [[homomorphism|homomorphisms]]. Here, mapping the input groups also maps their defect subgroups in the expected direction.'),
    'quotient map': entry('quotient map',
      'The natural [[surjective]] [[homomorphism]] from a [[group]] to a [[quotient group]], sending each element to the class obtained after the chosen subgroup is erased.'),
    'split epimorphism': entry('split epimorphism',
      'A [[surjective]] [[homomorphism]] with a reverse-direction homomorphism that chooses one original input for every output. “Epimorphism” here means onto, and “split” means this choice respects multiplication.'),
    'vertex group': entry('vertex group',
      'One of the original [[group|groups]] placed at the pieces, or vertices, of a construction such as an [[amalgamated free product]].'),
    'universal property': entry('universal property',
      'A rule characterizing an object by the maps into or out of it. Here it guarantees one and only one map from the joined group once compatible maps from its two pieces are given.'),
    'normal form': entry('normal form',
      'A standard, unambiguous way to write each element. For an [[amalgamated free product]], it alternates pieces from the two joined groups after shared pieces are simplified.'),
    'MF-visible': entry('MF-visible',
      'Detectable by at least one [[homomorphism]] to an [[MF group]] or [[norm matrix corona]], rather than being erased by every such map.'),
    'MF-invisible': entry('MF-invisible',
      'Erased by every allowed MF [[homomorphism]]. An MF-invisible element belongs to the [[MF radical]] and cannot be distinguished by the permitted finite-matrix tests.'),
    'topological closure': entry('topological closure',
      'The smallest closed [[set]] containing a given set: it adds every point that can be approached by points already present. This is not the paper’s algebraic MF closure.'),
    'marked group': entry('marked group',
      'A [[group]] together with an ordered list of chosen [[generator|generators]]. The marking lets different groups be compared using words in the same named generators.'),
    'criterion': entry('criterion',
      'A precise condition used to decide whether a claim holds. A criterion may give a sufficient condition, a necessary condition, or both.'),
    'hypothesis': entry('hypothesis',
      'An assumption made at the start of a theorem or argument. The conclusion is guaranteed only when all listed hypotheses hold.'),
    'theorem': entry('theorem',
      'A mathematical statement proved from earlier definitions and accepted facts. Its proof explains why its conclusion follows from its hypotheses.'),
    'lemma': entry('lemma',
      'A proved statement used mainly as a step toward a larger [[theorem]]. Calling it a lemma describes its role, not its difficulty.'),
    'proposition': entry('proposition',
      'A proved mathematical statement, usually presented as a useful result that is somewhat less central than a main [[theorem]].'),
    'corollary': entry('corollary',
      'A statement that follows quickly from a previously proved [[theorem]] or [[proposition]], with little additional argument.')
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
    '<': entry('strictly less than',
      'The numerical quantity on the left is smaller than the quantity on the right.', '<'),
    '≥': entry('greater than or equal to',
      'For numbers, the quantity on the left is at least the one on the right. For positive operators here, their difference is a positive operator.', '\\ge'),
    '⊴': entry('normal-subgroup containment',
      'The object on the left is a [[normal subgroup]] of the [[group]] on the right, so conjugating its elements by any element of the larger group keeps them inside it.', '\\trianglelefteq'),
    '⊆': entry('subset containment',
      'Every object belonging to the [[set]] on the left also belongs to the set on the right; the two sets are allowed to be equal.', '\\subseteq'),
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
      'Join groups without adding [[relation|equations]] that mix the two sides. A [[subscript]] names the shared [[subgroup]] that is identified.', '*'),
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
    'P': entry('the Kazhdan projection P', 'P is the [[projection]] onto the vectors fixed by every represented element of the property-(T) subgroup L.', 'P'),
    'p': entry('the Kazhdan projection p', 'p is the [[projection]] onto the vectors fixed by every represented element of the normal property-(T) subgroup K.', 'p'),
    'b': entry('the average movement operator b', 'b is the positive operator obtained by averaging the squared displacement caused by the elements of the chosen [[Kazhdan set]].', 'b'),
    'bn': entry('the stage-n average movement matrix b n', 'The [[subscript]] n selects the finite-stage positive matrix representing the average movement operator b.', 'b_n'),
    'o': entry('a quantity tending to zero', 'The notation \(o(1)\), read “little o of one,” means a numerical [[sequence]] whose [[limit]] is zero.', 'o(1)'),
    'S': entry('the Kazhdan set S', 'S is the chosen finite symmetric [[Kazhdan set]] inside K.', 'S'),
    's': entry('an element s of the Kazhdan set', 's is one [[element]] of the finite [[Kazhdan set]] S.', 's'),
    'R': entry('the ring R', 'R is the [[ring]], here a binary [[Leavitt algebra]], used for matrix entries.', 'R'),
    'S': entry('the ring S', 'S is a [[ring]] used for matrix entries.', 'S'),
    'N': entry('the subgroup N', 'N is a [[normal subgroup]] whose elements will be treated as the [[identity]] in a [[quotient group]].', 'N'),
    'f': entry('the map f', 'f is the [[surjective]] [[homomorphism]] from G onto Q.', 'f'),
    'π': entry('the map pi', 'The Greek letter pi names a [[homomorphism]] or [[representation]].', '\\pi'),
    'ρ': entry('the representation rho', 'The Greek letter rho names the [[representation]] that assigns an invertible linear operator to each element of G.', '\\rho'),
    'Θ': entry('the corona representation Theta', 'The Greek letter Theta names the [[homomorphism]] from G into the unitary group of a [[norm matrix corona]].', '\\Theta'),
    'Ψ': entry('the compression map Psi', 'The Greek letter Psi names the injective [[endomorphism]] that compresses a 3-by-3 matrix A into one Leavitt piece and uses q on the complementary diagonal piece.', '\\Psi'),
    'κ': entry('the Kazhdan constant kappa', 'The Greek letter kappa names a positive [[Kazhdan constant]] for the finite Kazhdan set S.', '\\kappa'),
    'ξ': entry('the vector xi', 'The Greek letter xi names a [[vector]] fixed by the represented subgroup L.', '\\xi'),
    'τ': entry('the matrix tau', 'The [[Greek letter]] tau names the [[invertible]] [[matrix]] that sends L back inside itself by [[conjugation]].', '\\tau'),
    'ℓ': entry('the element ell', 'The Greek letter ell names an [[element]] of the [[subgroup]] L.', '\\ell'),
    'u': entry('the element u', 'u is a [[group]] element used for [[conjugation]].', 'u'),
    'c': entry('the element c', 'c is a [[group]] element that commutes with every element of L.', 'c'),
    'h': entry('the element h', 'h is an arbitrary [[element]] of the [[subgroup]] L used in the displayed calculation.', 'h'),
    'd': entry('the element d', 'd is the concrete nonidentity [[group]] element whose [[normal closure]] becomes H.', 'd'),
    'q': entry('the algebra element q', 'q is the nonzero [[Leavitt algebra]] element \\(s_1t_1\\).', 'q'),
    'a': entry('the entry a', 'a is a variable [[element]], usually an entry from the surrounding [[ring]].', 'a'),
    'x': entry('the entry x', 'x is a variable [[element]] or one term in a [[sequence]], as specified by the surrounding formula.', 'x'),
    'g': entry('the element g', 'g is an arbitrary [[element]] of the [[group]] G.', 'g'),
    'V': entry('the asymptotic representation V', 'V names the complete [[sequence]] of finite-matrix maps in an [[asymptotic representation]].', 'V'),
    'Vn': entry('the stage-n map V n', 'The [[subscript]] n selects the nth finite-matrix map in the [[asymptotic representation]] V.', 'V_n'),
    'Wn': entry('the compressed stage-n map W n', 'The [[subscript]] n selects the nth exactly unitary map acting on the smaller [[corner]] chosen by the projection \(q_n\).', 'W_n'),
    'Un': entry('the lifted stage-n unitary U n', 'The [[subscript]] n selects a unitary matrix lift of the represented group element at stage n.', 'U_n'),
    'qn': entry('the stage-n corner projection q n', 'The [[subscript]] n selects the [[projection]] whose range is the smaller matrix [[corner]] used at stage n.', 'q_n'),
    'm': entry('the matrix-size variable m', 'm is a positive whole number used as the number of rows and columns in a square [[matrix]].', 'm'),
    'mn': entry('the stage-n matrix size m n', 'The [[subscript]] n selects the matrix size used at stage n of the [[sequence]].', 'm_n'),
    'Mmn': entry('the matrices of size m n', 'This is the [[set]] of square complex [[matrix|matrices]] having \(m_n\) rows and \(m_n\) columns.', 'M_{m_n}'),
    'I': entry('an identity matrix I', 'I denotes an [[identity matrix]] whose size is determined by the surrounding block-matrix formula.', 'I'),
    'I3': entry('the 3-by-3 identity matrix', 'The [[subscript]] 3 specifies that this is the [[identity matrix]] with three rows and three columns.', 'I_3'),
    'I9': entry('the 9-by-9 identity matrix', 'The [[subscript]] 9 specifies that this is the [[identity matrix]] with nine rows and nine columns.', 'I_9'),
    'X': entry('the block matrix X', 'X is the 6-by-6 [[matrix]] defined from four 3-by-3 blocks using the Leavitt generators; the following calculation shows that Y is its [[inverse]].', 'X'),
    'Y': entry('the block matrix Y', 'Y is the 6-by-6 [[matrix]] defined from four 3-by-3 blocks and is the [[inverse]] of X.', 'Y'),
    'K2': entry('the Hilbert–Schmidt kernel K two', 'This is the [[normal subgroup]] of elements that the chosen asymptotic representation V sends toward the [[identity]] in normalized [[Hilbert–Schmidt norm]].', 'K_2'),
    'R∞→2': entry('the universal infinity-to-two kernel', 'This [[normal subgroup]] contains the elements that every operator-norm [[asymptotic representation]] sends toward the [[identity]] in normalized [[Hilbert–Schmidt norm]].', 'R_{\\infty\\to2}'),
    'C2': entry('the asymptotic commutant C two', 'This symbol names the [[asymptotic commutant]] of the representation V and the subgroup L, measured using normalized [[Hilbert–Schmidt norm]].', '\\mathcal C_2'),
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
      'The [[calligraphic letter|calligraphic]] Q is the chosen name for this [[norm matrix corona]].', '\\mathcal Q');
    if (symbol === 'C' && /\\C|\\mathbb\s*\{?C/.test(tex || '')) return entry('the complex-number symbol C',
      'The [[blackboard-bold letter|blackboard-style]] C names the [[complex number|complex numbers]].', '\\mathbb C');
    if (symbol === 'C' && /C_[GH]/.test(tex || '')) return entry('the centralizer symbol C',
      'Here C names a [[centralizer]] inside the group shown as its subscript.', 'C');
    if (symbol === 'C' && /\\mathcal\s*C_2/.test(tex || '')) return entry('the asymptotic-commutant symbol C',
      'The [[calligraphic letter|calligraphic]] C is the chosen name for this [[asymptotic commutant]].', '\\mathcal C');
    if (symbol === 'M' && /M_\{?d_n/.test(tex || '')) return entry('the matrix-set symbol M',
      'M names a [[set]] of square [[matrix|matrices]]. Its subscript gives the number of rows and columns.', 'M');
    if (symbol === 'd' && /\\mathbf\s*d/.test(tex || '')) return entry('the matrix-size sequence d',
      'The [[bold letter]] d names the [[sequence]] of matrix sizes. Its nth entry is written \\(d_n\\).', '\\mathbf d');
    if (symbol === 'f' && /f\(q,a\)/.test(tex || '')) return entry('the map f from W sub Q to T',
      'Here f is an arbitrary [[homomorphism]] from the constructed group \\(W_Q\\) to the target group T. The calculation shows that it ignores the A-coordinate.', 'f');
    if (symbol === 'q' && /f\(q,a\)/.test(tex || '')) return entry('the Q-coordinate q',
      'Here q is an arbitrary [[element]] of the group Q and is the first coordinate of the [[ordered pair]] \\((q,a)\\). It is unrelated to the Leavitt-algebra element also named q.', 'q');
    if (symbol === 'a' && /f\(q,a\)/.test(tex || '')) return entry('the A-coordinate a',
      'Here a is an arbitrary [[element]] of the subgroup A and is the second coordinate of the [[ordered pair]] \\((q,a)\\). The map f sends this coordinate to the identity.', 'a');
    if ((symbol === 'Z' || symbol === 'ℤ') && /\\mathbb\s*\{?Z/.test(tex || '')) return entry('the group of integers',
      'The blackboard-style letter \\(\mathbb Z\\) names the [[group of integers]] under addition.', '\\mathbb Z');
    if (symbol === 'q' && /q_n|q\\Theta|\\mathcal Q|q-q/.test(tex || '')) return entry('the complementary projection q',
      'q is the [[projection]] complementary to p, defined by \(q=1-p\). It is the identity element of the smaller [[corner]] used in the argument.', 'q');
    if (symbol === 'p' && /p=s_0t_0|p\+q=1/.test(tex || '')) return entry('the Leavitt element p',
      'p abbreviates the product \(s_0t_0\) in the binary [[Leavitt algebra]]. Together with q it satisfies \(p+q=1\).', 'p');
    if (symbol === 'A' && /A=g|1-BA|AB=0/.test(tex || '')) return entry('the conjugated matrix-unit part A',
      'A is the conjugate by g of a matrix unit, possibly multiplied by a ring coefficient. It is chosen so that its product AB is zero.', 'A');
    if (symbol === 'B' && /B=(?:b)?E|1-BA|AB=0/.test(tex || '')) return entry('the original matrix-unit part B',
      'B is a matrix unit, possibly multiplied by a ring coefficient, chosen so that AB is zero while BA retains a useful row.', 'B');
    if (symbol === 'b' && /axb=1|arb=0|a=f_s/.test(tex || '')) return entry('the right sandwich factor b',
      'b is a [[ring]] element chosen as a right-hand multiplier in the displayed sandwich or coefficient-separation identity.', 'b');
    if (symbol === 'c' && /cwd|t_1c|t_1c/.test(tex || '')) return entry('the left sandwich factor c',
      'c is a [[ring]] element chosen so that multiplying w by c on the left and d on the right gives the identity.', 'c');
    if (symbol === 'd' && /cwd|ds_0/.test(tex || '')) return entry('the right sandwich factor d',
      'd is a [[ring]] element chosen so that multiplying w by c on the left and d on the right gives the identity.', 'd');
    if (symbol === 'w' && /e_\{(?:wu|vw|uw)\}/.test(tex || '')) return entry('the third matrix index w',
      'w is a row or column [[index]] chosen different from u and v so that the elementary-matrix commutator rule applies.', 'w');
    if (symbol === 'w') return entry('the ring element w',
      'w is the [[ring]] element to which the coefficient-separation construction is being applied.', 'w');
    if (symbol === 'v' && /1\+v|v_\{im\}/.test(tex || '')) return entry('the one-row square-zero matrix v',
      'v is the nonzero [[matrix]] supported in row i whose square is zero. The element \(1+v\) belongs to the normal subgroup N.', 'v');
    if (symbol === 'v') return entry('the matrix index v',
      'v is a row or column [[index]] on the displayed elementary matrices.', 'v');
    if (symbol === 'vim') return entry('the i-m entry of v',
      'This is the entry of the [[matrix]] v in row i and column m, chosen to be nonzero.', 'v_{im}');
    if (symbol === 'im') return entry('row i and column m',
      'The first letter i selects a matrix row and the second letter m selects a matrix column.', 'im');
    if (symbol === 'r') return entry('the ring coefficient r',
      'r is an arbitrary [[ring]] element used as the coefficient of the displayed elementary matrices.', 'r');
    if (symbol === 'y') return entry('the auxiliary ring element y',
      'y is the [[ring]] element constructed as part of the coefficient-separation argument.', 'y');
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
    if (symbol === '([') return entry('function and commutator opening marks',
      'The parenthesis begins the input to a [[function]], and the square bracket begins the [[commutator]] placed inside that input.', '([');
    if (symbol === '])') return entry('commutator and function closing marks',
      'The square bracket ends the [[commutator]], and the parenthesis ends the input supplied to the surrounding [[function]].', '])');
    if (symbol === ')]') return entry('function and commutator closing marks',
      'The parenthesis ends the coefficient supplied to the [[elementary matrix]], and the square bracket ends the surrounding [[commutator]].', ')]');
    if (symbol === '0.') return entry('zero followed by end punctuation',
      'Zero is the stated [[limit]], and the period ends the mathematical sentence.', '0.');
    if (symbol === '∣S∣1' || symbol === '∣S∣' || symbol === '∣') return entry('reciprocal of the size of S',
      'The vertical bars around S mean the number of elements in the finite [[set]] S. The fraction (1/|S|) divides by that number to form an average.', '\\frac1{|S|}');
    if (symbol === 's∈S∑' || symbol === 's∈S' || symbol === '∑') return entry('sum over the elements of S',
      'Add one copy of the following expression for every [[element]] s belonging to the finite [[set]] S.', '\\sum_{s\\in S}');
    if (symbol === 'κ2') return entry('the squared Kazhdan constant',
      'The superscript 2 means multiply the positive [[Kazhdan constant]] kappa by itself.', '\\kappa^2');
    if (symbol === '∣S∣κ2') return entry('Kazhdan lower-bound coefficient',
      'This is the squared [[Kazhdan constant]] divided by the number of elements in the finite Kazhdan set S.', '\\frac{\\kappa^2}{|S|}');
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
    if (symbol.endsWith('−1')) return entry('inverse exponent',
      'The superscript −1 means [[inverse]]: the operation that undoes the named group element, matrix, or map.', '^{-1}');
    if (symbol.endsWith('′')) return entry('commutant prime',
      'The prime mark after a represented [[subgroup]] means its [[commutant]]: all linear operators that commute with every represented element of that subgroup.', "'");
    if (symbol === 'RadMF' || symbol === 'Rad' || symbol === 'MF') return entry('the MF-radical label',
      'These letters are parts of the symbol for the [[MF radical]]. [[MF]] names the approximation rule and “Rad” abbreviates [[radical]].', '\\operatorname{Rad}_{\\mathrm{MF}}');
    if (symbol === 'ker') return entry('kernel abbreviation',
      'The letters ker abbreviate [[kernel]]: all inputs that the following map sends to the [[identity]].', '\\ker');
    if (symbol === 'Hom') return entry('homomorphism-set abbreviation',
      'The letters Hom name the [[set]] of all [[homomorphism|homomorphisms]] from the group listed first to the group listed second.', '\\operatorname{Hom}');
    if (symbol === 'diag') return entry('block-diagonal construction',
      'Place the listed [[matrix|matrices]] along the main [[diagonal]] as blocks and fill every off-diagonal block with zeros.', '\\operatorname{diag}');
    if (symbol === 'GL' || /^GL\d+$/.test(symbol)) return entry('general linear group',
      'The letters GL name the [[general linear group]] of all invertible square matrices of the indicated size over the indicated ring.', '\\operatorname{GL}');
    if (symbol === 'Ad') return entry('conjugation operation Ad',
      'The abbreviation Ad means [[conjugation]]. Applied to a unitary A, it is the operation sending each matrix x to \(AxA^*\).', '\\operatorname{Ad}');
    if (symbol === 'trd' || symbol === 'tr') return entry('normalized trace',
      'This is the [[trace]] divided by the matrix size d. It averages the diagonal entries instead of summing them, so matrices of different sizes can be compared.', '\\operatorname{tr}_d');
    if (symbol === 'Tr') return entry('ordinary trace',
      'The capitalized letters Tr mean the [[trace]]: add all entries on the main [[diagonal]] of the square matrix.', '\\operatorname{Tr}');
    if (symbol === 'sup' || symbol === 'nsup') return entry('supremum over n',
      'Take the least numerical upper bound that works for the displayed quantities at every stage n. Requiring it to be finite says the entire [[sequence]] is [[uniformly bounded]].', '\\sup_n');
    if (symbol === '∞→2') return entry('infinity-to-two norm label',
      'This [[subscript]] says that the approximations are controlled in operator norm, conventionally called the infinity norm, while the conclusion is measured in the Schatten 2 or [[Hilbert–Schmidt norm]].', '\\infty\\to2');
    if (symbol === '∞') return entry('infinity-norm label',
      'Here infinity labels the [[operator norm]], which is also called the Schatten infinity norm.', '\\infty');
    if (symbol.endsWith('∗')) return entry('adjoint star',
      'The superscript star means the [[adjoint]], obtained by transposing the matrix and taking the complex conjugate of every entry.', '^*');
    if (symbol === '1/2' || symbol === ')1/2') return entry('square-root exponent',
      'Raising a nonnegative number to the power one half means taking its nonnegative square root.', '^{1/2}');
    if (symbol === 'd1') return entry('normalizing factor one over d',
      'This fraction is one divided by d, where d is the matrix size. Multiplying the ordinary trace by it produces the normalized trace.', '\\frac1d');
    if (symbol === 'isMF') return entry('is an MF group',
      'The preceding [[quotient group]] satisfies the definition of an [[MF group]].', '\\text{is MF}');
    if (symbol === 'and') return entry('logical and',
      'Both the condition before this word and the condition after it must be true.', '\\text{and}');
    if (symbol === 'Mdn') return entry('the matrix set at stage n',
      'This is the [[set]] of square [[matrix|matrices]] with \\(d_n\\) rows and columns and [[complex number|complex-number]] entries.', 'M_{d_n}(\\mathbb C)');
    if (symbol === 'Qd') return entry('the chosen norm matrix corona',
      'The [[calligraphic letter|calligraphic]] Q names a [[norm matrix corona]], and the [[subscript]] d records its [[sequence]] of matrix sizes.', '\\mathcal Q_{\\mathbf d}');
    if (symbol === 'U') return entry('the unitary-elements symbol U',
      'U selects the [[unitary matrix|unitary elements]] inside the surrounding matrix object.', '\\mathcal U');
    if (/^π:G→U\(Qd\)$/.test(symbol)) return entry('a representation pi from G',
      'The [[Greek letter]] pi names a [[homomorphism]] from the [[group]] G to the [[unitary matrix|unitary elements]] of the [[norm matrix corona]].', '\\pi\\colon G\\to\\mathcal U(\\mathcal Q_{\\mathbf d})');
    if (symbol === 'Comp' || symbol === 'CompG') return entry('the compression-set label',
      'Comp abbreviates the [[set]] of group elements whose [[conjugation]] sends L back inside L. A subscript G names the surrounding [[group]].', '\\operatorname{Comp}_G');
    if (symbol === 'D' || symbol === 'DG' || symbol === 'DQ') return entry('the compression-defect label',
      'The [[fraktur letter|ornate D]] is the chosen name for the [[normal closure]] of the compression [[commutator|commutators]].', '\\mathfrak D');
    if (symbol === 'Df(G)') return entry('the defect inside the image group',
      'This is the compression-centralizer defect formed inside the [[image]] group \(f(G)\), using the subgroup \(f(L)\).', '\\mathfrak D_{f(G)}');
    if (symbol === 'f(G)') return entry('the image group f of G',
      'This is the [[subgroup]] consisting of all outputs \(f(g)\) as g ranges over G.', 'f(G)');
    if (/^[stI0-3]+$/.test(symbol) && /[st][01]/.test(symbol)) return entry('a Leavitt block-matrix entry',
      'This is an entry, row, or complete flattened view of a block [[matrix]]. Adjacent Leavitt symbols are multiplied in order, and \(I_3\) is the 3-by-3 [[identity matrix]].', symbol);
    if (/^[IX0−1]+$/.test(symbol) && symbol.length > 1) return entry('entries of a Whitehead block factor',
      'These are the entries of one 2-by-2 block [[matrix]] in the Whitehead factorization. I is the 6-by-6 [[identity matrix]], 0 is the zero block, and a minus sign takes an additive opposite.', symbol);
    if (/^e[a-zℓ]{2}$/.test(symbol)) return entry('an elementary-matrix symbol',
      'The letter e names an [[elementary matrix]], and the two following letters give its row and column [[index|indices]]. The coefficient appears in parentheses after it.', symbol);
    if (/^E[a-zℓ]{2}$/.test(symbol)) return entry('a matrix-unit symbol',
      'The capital E names a [[matrix unit]] with one entry equal to 1 and all other entries zero. The two following symbols give its row and column.', symbol);
    if (symbol === 'iℓ') return entry('row i and column ell',
      'The first symbol i selects the row and the second symbol ell selects the column of the surrounding [[matrix unit]] or [[elementary matrix]].', 'i\\ell');
    if (/^[a-zℓ]{2}$/.test(symbol) && ((tex || '').indexOf('e_{' + symbol + '}') >= 0 || (tex || '').indexOf('E_{' + symbol + '}') >= 0)) return entry('row and column indices',
      'The first letter selects the row and the second selects the column of the extra entry in the surrounding [[elementary matrix]].', symbol);
    if (/^(?:c|d|e|f)[rdst]$/.test(symbol)) return entry('a labeled sandwich factor',
      'The main letter names a chosen [[ring]] multiplier. Its [[subscript]] records which element or factorization that choice belongs to, so the several auxiliary multipliers remain distinct.', symbol);
    if (symbol === 'CG') return entry('the centralizer in G',
      'This is the [[centralizer]] of L computed inside the [[group]] G.', 'C_G');
    if (symbol === '⟨' || symbol === '⟩') return entry('normal-closure bracket',
      'The doubled angle brackets enclose generators of a [[normal closure]]. A following subscript names the surrounding group.', '\\langle\\!\\langle d\\rangle\\!\\rangle');
    if (symbol === 'F') return entry('the field symbol F',
      'The [[blackboard-bold letter|blackboard-style]] F names a [[field]]. The following [[subscript]] tells which field.', '\\mathbb F');
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
    if (/^WZ$/.test(symbol) && /\\mathbb\s*\{?Z/.test(tex || '')) return entry('the group W sub Z',
      'This is the constructed [[group]] W built using the [[group of integers]] \\(\mathbb Z\\). The subscript records that concrete choice of Q.', 'W_{\\mathbb Z}');
    if (/^πQ$/.test(symbol)) return entry('the map pi sub Q',
      'This [[homomorphism]] sends the group \\(W_Q\\) onto Q. The subscript Q names its destination.', '\\pi_Q');
    if (/^CH$/.test(symbol)) return entry('the centralizer in H',
      'This is the [[centralizer]] computed inside the [[group]] H.', 'C_H');
    if (/^clMFG$/.test(symbol)) return entry('MF closure inside G',
      'This symbol names the MF [[closure operation]] performed inside the [[group]] G.', '\\operatorname{cl}_{\\mathrm{MF}}^G');
    if (/^clMFWQ$/.test(symbol)) return entry('MF closure inside W sub Q',
      'This symbol names the MF [[closure operation]] performed inside the constructed [[group]] \\(W_Q\\).', '\\operatorname{cl}_{\\mathrm{MF}}^{W_Q}');
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

  var TERM_ALIASES = {
    'circled-plus sign': ['circled plus sign', 'circled plus signs'],
    'embedding': ['embed', 'embeds', 'embedded', 'embedding'],
    'unitary matrix': ['unitary', 'unitaries'],
    'faithful': ['faithful', 'faithfully', 'faithfulness'],
    'injective': ['injective', 'injectively', 'injectivity'],
    'surjective': ['surjective', 'surjectively', 'surjectivity', 'onto'],
    'bijection': ['bijection', 'bijections', 'bijective', 'bijectively'],
    'commute': ['commute', 'commutes', 'commuted', 'commuting', 'centralizes'],
    'normal subgroup': ['normal subgroup', 'normal subgroups', 'normality'],
    'normal generation': [
      'normal generation', 'normally generate', 'normally generates',
      'normally generated', 'normal generator'
    ],
    'factors through': [
      'factor through', 'factors through', 'factored through', 'factorization'
    ],
    'unital': ['unital', 'unitality'],
    'lift': ['lift', 'lifts', 'lifted', 'lifting', 'coordinate unitary lifts'],
    'polar correction': ['polar correction', 'polar-correcting', 'polar-corrected'],
    'unitarily equivalent': [
      'unitarily equivalent', 'unitary equivalence', 'unitarily equivalence'
    ],
    'stably finite': ['stably finite', 'stable finiteness'],
    'projection domination': ['projection domination', 'dominated', 'dominated by'],
    'corona norm': ['corona norm', 'corona-norm', 'quotient norm'],
    'MF closure': ['MF closure', 'MF-kernel closure'],
    'fixed vector': ['fixed vector', 'fixed vectors', 'fixed-space'],
    'nondegenerate representation': [
      'nondegenerate representation', 'nondegenerate representations',
      'nondegenerately'
    ],
    'unitarity error': [
      'unitarity error', 'unitarity errors', 'unitarity defect', 'unitarity defects'
    ],
    'universal Hilbert–Schmidt kernel': [
      'universal Hilbert–Schmidt kernel', 'universal Hilbert--Schmidt kernel'
    ],
    'Hilbert-space ultraproduct': [
      'Hilbert-space ultraproduct', 'ultraproduct of Hilbert spaces'
    ],
    'non-approximability': ['non-approximability', 'failure of approximation'],
    'double of a group': ['double', 'doubles'],
    'root extraction': ['root extraction', 'root-extraction'],
    'purely infinite simple': ['purely infinite simple', 'pure infiniteness'],
    'C-star algebra': ['C*-algebra', 'C*-algebras'],
    'star-homomorphism': ['*-homomorphism', '*-homomorphisms'],
    'Hilbert–Schmidt norm': [
      'Hilbert–Schmidt norm', 'Hilbert–Schmidt norms',
      'Hilbert-Schmidt norm', 'Hilbert-Schmidt norms'
    ],
    'normalized Hilbert–Schmidt norm': [
      'normalized Hilbert–Schmidt norm', 'normalized Hilbert–Schmidt norms',
      'normalized Hilbert-Schmidt norm', 'normalized Hilbert-Schmidt norms'
    ],
    'multiplication error': [
      'multiplication defect', 'multiplication defects',
      'multiplicative defect', 'multiplicative defects'
    ],
    'asymptotic': ['asymptotic', 'asymptotically'],
    'separate elements': ['separate', 'separates', 'separated', 'separating'],
    'nonidentity': ['nonidentity', 'non-identity'],
    'property (T)': ['property (T)', 'property-(T)'],
    'MF': ['MF', 'non-MF', 'MF-ness', 'group-MF'],
    'MF group': ['MF group', 'MF groups'],
    'MF-visible': ['MF-visible', 'MF visible', 'visible to MF'],
    'MF-invisible': ['MF-invisible', 'MF invisible', 'invisible to MF'],
    'MF radical': ['MF radical', 'MF radicals', 'MF-radical'],
    'norm matrix corona': ['norm matrix corona', 'norm matrix coronas'],
    'c0-direct sum': ['c0-direct sum', 'c₀-direct sum'],
    'finite-matrix model': ['finite-matrix model', 'finite-matrix models'],
    'asymptotic representation': [
      'asymptotic representation', 'asymptotic representations'
    ]
  };

  function termForms(term) {
    var plural;
    if (term === 'matrix') plural = 'matrices';
    else if (/[^aeiou]y$/.test(term)) plural = term.slice(0, -1) + 'ies';
    else if (/(?:s|x|ch|sh)$/.test(term)) plural = term + 'es';
    else plural = term + 's';
    var forms = plural === term ? [term] : [term, plural];
    return forms.concat(TERM_ALIASES[term] || []).filter(function (form, index, all) {
      return all.indexOf(form) === index;
    });
  }

  var TERM_MATCHERS = [];
  Object.keys(TERMS).forEach(function (term) {
    termForms(term).forEach(function (form) {
      TERM_MATCHERS.push({ term: term, form: form });
    });
  });
  TERM_MATCHERS.sort(function (left, right) {
    return right.form.length - left.form.length;
  });

  function termAt(text, offset, excludedTerm) {
    var lower = text.toLowerCase();
    for (var i = 0; i < TERM_MATCHERS.length; i++) {
      var term = TERM_MATCHERS[i].term;
      if (term === excludedTerm) continue;
      var form = TERM_MATCHERS[i].form;
      if (lower.slice(offset, offset + form.length) !== form.toLowerCase()) continue;
      var before = offset ? text[offset - 1] : '';
      var after = text[offset + form.length] || '';
      if (/[A-Za-z0-9]/.test(before) || /[A-Za-z0-9]/.test(after)) continue;
      return { term: term, length: form.length };
    }
    return null;
  }

  function termMatches(value, excludedTerm) {
    var text = String(value || '');
    var result = [];
    var cursor = 0;
    while (cursor < text.length) {
      var match = termAt(text, cursor, excludedTerm);
      if (!match) {
        cursor++;
        continue;
      }
      result.push({
        term: match.term,
        start: cursor,
        end: cursor + match.length,
        text: text.slice(cursor, cursor + match.length)
      });
      cursor += match.length;
    }
    return result;
  }

  function linkedTerms(value, excludedTerm) {
    var result = [];
    var seen = {};

    function add(term) {
      if (!TERMS[term] || term === excludedTerm || seen[term]) return;
      seen[term] = true;
      result.push(term);
    }

    function scanPlainText(value) {
      var text = String(value || '');
      var cursor = 0;
      while (cursor < text.length) {
        var match = termAt(text, cursor, excludedTerm);
        if (!match) {
          cursor++;
          continue;
        }
        add(match.term);
        cursor += match.length;
      }
    }

    var text = String(value || '');
    var cursor = 0;
    var pattern = /\[\[([^|\]]+)(?:\|([^\]]+))?\]\]|\\\(([\s\S]*?)\\\)/g;
    var match;
    while ((match = pattern.exec(text))) {
      if (match.index > cursor) scanPlainText(text.slice(cursor, match.index));
      if (match[3] == null) add(clean(match[1]));
      cursor = pattern.lastIndex;
    }
    if (cursor < text.length) scanPlainText(text.slice(cursor));
    return result;
  }

  function glossaryEntries() {
    return Object.keys(TERMS).map(function (term) {
      return {
        term: term,
        name: TERMS[term].name,
        explanation: TERMS[term].explanation,
        tex: TERMS[term].tex
      };
    });
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

  function proseNodeIsExcluded(node) {
    var parent = node && node.parentElement;
    if (!parent || !parent.closest) return true;
    return Boolean(parent.closest(
      'a, button, script, style, textarea, code, pre, .katex, .math-explainer, ' +
      '.math-help-prompt, [aria-hidden="true"]'));
  }

  function decorateProse(root) {
    if (!root || !document.createTreeWalker) return;
    var walker = document.createTreeWalker(root, 4);
    var nodes = [];
    var node;
    while ((node = walker.nextNode())) nodes.push(node);
    for (var i = 0; i < nodes.length; i++) {
      var textNode = nodes[i];
      if (proseNodeIsExcluded(textNode)) continue;
      var text = textNode.nodeValue || '';
      var matches = termMatches(text);
      if (!matches.length) continue;
      var fragment = document.createDocumentFragment();
      var cursor = 0;
      for (var j = 0; j < matches.length; j++) {
        var match = matches[j];
        if (match.start > cursor) {
          fragment.appendChild(document.createTextNode(text.slice(cursor, match.start)));
        }
        var button = document.createElement('button');
        button.type = 'button';
        button.className = 'math-term-help paper-term-help';
        button.setAttribute('data-term', match.term);
        button.setAttribute('aria-label', 'Explain ' + match.text);
        button.textContent = match.text;
        fragment.appendChild(button);
        cursor = match.end;
      }
      if (cursor < text.length) {
        fragment.appendChild(document.createTextNode(text.slice(cursor)));
      }
      textNode.parentNode.replaceChild(fragment, textNode);
    }
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
    box.classList.toggle('math-explainer-formula', Boolean(state.wholeFormula));
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

  function openTerm(term, pin) {
    var canonical = clean(term);
    var info = explainTerm(canonical);
    if (!info) return;
    if (current && current.term !== canonical) history.push(current);
    pinned = Boolean(pin);
    render({ symbol: canonical, info: info, term: canonical });
  }

  function goBack() {
    if (history.length) render(history.pop());
  }

  function closePanel() {
    if (!panel) return;
    panel.hidden = true;
    panel.classList.remove('math-explainer-formula');
    history = [];
    current = null;
    pinned = false;
    var opener = lastObject;
    lastObject = null;
    if (opener && opener.blur && document.activeElement === opener) opener.blur();
  }

  function openObject(node, math) {
    var info = node.__mathExplanation;
    if (!info) return;
    history = [];
    pinned = true;
    render({
      symbol: clean(node.textContent),
      info: info,
      term: '',
      wholeFormula: node.classList.contains('math-formula-help')
    });
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
    prompt.textContent = 'Hover over vocabulary or highlighted math for plain-language explanations. You can also click or use the keyboard.';
    anchor.insertAdjacentElement('afterend', prompt);
  }

  document.addEventListener('click', function (event) {
    var term = event.target.closest && event.target.closest('.math-term-help');
    if (term) {
      event.preventDefault(); event.stopPropagation();
      lastObject = term;
      openTerm(term.getAttribute('data-term'), true); return;
    }
    if (event.target.closest && event.target.closest('.math-explainer')) return;
    var object = event.target.closest && event.target.closest('.math-symbol-help, .math-formula-help');
    var math = object && (object.classList.contains('katex') ? object : object.closest('.katex'));
    if (object && math) {
      event.preventDefault(); event.stopPropagation(); openObject(object, math); return;
    }
    if (panel && !panel.hidden) closePanel();
  }, true);

  function previewPaperTerm(node) {
    if (!node || pinned) return;
    var canonical = clean(node.getAttribute('data-term'));
    var info = explainTerm(canonical);
    if (!info) return;
    lastObject = node;
    history = [];
    pinned = false;
    render({ symbol: canonical, info: info, term: canonical });
  }

  document.addEventListener('mouseover', function (event) {
    previewPaperTerm(event.target.closest && event.target.closest('.paper-term-help'));
  }, true);

  document.addEventListener('mouseout', function (event) {
    var term = event.target.closest && event.target.closest('.paper-term-help');
    if (!term || pinned || (event.relatedTarget && term.contains(event.relatedTarget))) return;
    closePanel();
  }, true);

  document.addEventListener('focusin', function (event) {
    previewPaperTerm(event.target.closest && event.target.closest('.paper-term-help'));
  }, true);

  document.addEventListener('focusout', function (event) {
    var term = event.target.closest && event.target.closest('.paper-term-help');
    if (!term || pinned || (event.relatedTarget && term.contains(event.relatedTarget))) return;
    closePanel();
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
    decorateProse(document.getElementById('abstract-body'));
    decorateProse(document.getElementById('paper-body'));
    decorate(document);
    addPrompt();
    var observer = new MutationObserver(function (records) {
      for (var i = 0; i < records.length; i++) {
        for (var j = 0; j < records[i].addedNodes.length; j++) {
          var node = records[i].addedNodes[j];
          if (node.nodeType !== 1) continue;
          decorateProse(node);
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
    linkedTerms: linkedTerms,
    glossaryEntries: glossaryEntries,
    termMatches: termMatches,
    decorateProse: decorateProse,
    renderTex: renderTex,
    decorate: decorate
  };
}());
