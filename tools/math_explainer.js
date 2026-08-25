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
      'A collection of reversible moves. Two moves can be performed in succession, there is a do-nothing move, and every move can be undone.'),
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
      'Here “corona” is a conventional name for a [[quotient]] of [[sequence|sequences]]: it keeps their long-run behavior but treats two sequences as equal [[modulo c0|when their difference tends to zero]]. It has nothing to do with the Sun.'),
    'norm matrix corona': entry('norm matrix corona',
      'A [[corona]] made from [[bounded sequence|bounded sequences]] of finite [[matrix|matrices]]. Two sequences count as the same when the [[operator norm]] of their difference has [[limit]] zero.'),
    'corona norm': entry('corona norm',
      'The size of an element in a [[norm matrix corona]]. For a representing matrix [[sequence]], it is the limiting upper size measured by [[operator norm]], unchanged by errors tending to zero.'),
    'c0-direct sum': entry('c0-direct sum',
      'The [[direct sum]] of matrix [[sequence|sequences]] whose [[operator norm|operator norms]] approach zero. The “c-zero” label is the conventional name for sequences that vanish in the long run.'),
    'MF': entry('MF',
      'MF stands for “matricial field,” the historical name for this finite-matrix [[approximation]] rule. To pass the MF test, [[multiplication error|multiplication errors]] must shrink to zero and different [[group]] elements must remain distinguishable.'),
    'MF group': entry('MF group',
      'A [[group]] that has a [[faithful]] [[representation]] by sequences of finite [[unitary matrix|unitary matrices]] in a [[norm matrix corona]]. Equivalently, its [[multiplication error|multiplication errors]] approach zero in [[operator norm]] without merging distinct group elements.'),
    'MF radical': entry('MF radical',
      'The [[radical]] for the MF test: the [[normal subgroup]] of elements erased by every [[homomorphism]] from the group into every [[norm matrix corona]]. This subgroup is [[fully invariant]].'),
    'radical': entry('radical',
      'In this paper, “radical” means the largest part of a [[group]] that all allowed tests erase. It is unrelated to a square-root sign.'),
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
    'R': entry('the ring R', 'R is the [[ring]], here a binary [[Leavitt algebra]], used for matrix entries.', 'R'),
    'S': entry('the ring S', 'S is a [[ring]] used for matrix entries.', 'S'),
    'N': entry('the subgroup N', 'N is a [[normal subgroup]] whose elements will be treated as the [[identity]] in a [[quotient group]].', 'N'),
    'f': entry('the map f', 'f is the [[surjective]] [[homomorphism]] from G onto Q.', 'f'),
    'π': entry('the map pi', 'The Greek letter pi names a [[homomorphism]] or [[representation]].', '\\pi'),
    'τ': entry('the matrix tau', 'The [[Greek letter]] tau names the [[invertible]] [[matrix]] that sends L back inside itself by [[conjugation]].', '\\tau'),
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
      'The [[calligraphic letter|calligraphic]] Q is the chosen name for this [[norm matrix corona]].', '\\mathcal Q');
    if (symbol === 'C' && /\\C|\\mathbb\s*\{?C/.test(tex || '')) return entry('the complex-number symbol C',
      'The [[blackboard-bold letter|blackboard-style]] C names the [[complex number|complex numbers]].', '\\mathbb C');
    if (symbol === 'C' && /C_[GH]/.test(tex || '')) return entry('the centralizer symbol C',
      'Here C names a [[centralizer]] inside the group shown as its subscript.', 'C');
    if (symbol === 'M' && /M_\{?d_n/.test(tex || '')) return entry('the matrix-set symbol M',
      'M names a [[set]] of square [[matrix|matrices]]. Its subscript gives the number of rows and columns.', 'M');
    if (symbol === 'd' && /\\mathbf\s*d/.test(tex || '')) return entry('the matrix-size sequence d',
      'The [[bold letter]] d names the [[sequence]] of matrix sizes. Its nth entry is written \\(d_n\\).', '\\mathbf d');
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
      'These letters are parts of the symbol for the [[MF radical]]. [[MF]] names the approximation rule and “Rad” abbreviates [[radical]].', '\\operatorname{Rad}_{\\mathrm{MF}}');
    if (symbol === 'ker') return entry('kernel abbreviation',
      'The letters ker abbreviate [[kernel]]: all inputs that the following map sends to the [[identity]].', '\\ker');
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
    if (symbol === 'D') return entry('the compression-defect label',
      'The [[fraktur letter|ornate D]] is the chosen name for the [[normal closure]] of the compression [[commutator|commutators]].', '\\mathfrak D');
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

  var TERM_ALIASES = {
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
    'MF-visible': ['MF-visible', 'MF visible'],
    'MF-invisible': ['MF-invisible', 'MF invisible'],
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
    prompt.textContent = 'Click underlined vocabulary or highlighted math for plain-language explanations.';
    anchor.insertAdjacentElement('afterend', prompt);
  }

  document.addEventListener('click', function (event) {
    var term = event.target.closest && event.target.closest('.math-term-help');
    if (term) {
      event.preventDefault(); event.stopPropagation();
      lastObject = term;
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
