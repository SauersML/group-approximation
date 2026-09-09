# Arithmetic shell maps and the deterministic finite-state boundary, 2026-09-08

The direct perfect-input shell route remains open. The group A_5 * A_5
is an explicit perfect finitely presented decidable input occurring in
the perfect-envelope construction. It is a useful test of attempts to
obtain presentations beyond the virtually cyclic positive control.

## A sharper finite-state obstruction

A suffix-preserving shell map h_pi fixes 0^infinity. In a deterministic
finite-state transducer, reading this all-zero input eventually traverses
one state cycle. If it consumes m zeros and emits a zeros per cycle,
then pi(n+m)=pi(n)+a for all sufficiently large n. The m source residue
rays have disjoint image tails of step a, and bijectivity makes them
exhaust all a target residue rays. Hence a=m.

Conversely an eventual m-periodic shell permutation has bounded
displacement and can be implemented with a finite initial output delay
and finite residue memory. Thus rational shell maps are exactly the
eventually periodic translations of shell indices.

Taking a common period across finitely many generators and using the
input's free even-index orbit proves that a finitely generated infinite
input admits this rational regular shell action exactly when it is
virtually cyclic. This is a restriction on the concrete shell action,
not on all rational embeddings of the abstract input.

In particular an arithmetic formula whose slope varies between residue
classes is not, for that reason, a deterministic finite-state transducer.
The all-zero cycle cannot choose its output rate based on a residue it
will only learn when the arbitrarily distant first 1 is read.

## An exact arithmetic benchmark with decidable word problem

For A_5*A_5, assign digits 1,...,59 to the nonidentity factor elements.
Encode a nonempty alternating reduced word by its first factor type
epsilon and the bijective-base integer q=sum d_j*59^(j-1), with the
first syllable least significant. Put nu=2*q-1+epsilon and nu(1)=0.

Left multiplication either prepends a digit, replaces the first digit,
or removes it after cancellation. The corresponding arithmetic slopes
are 59, 1, and 1/59, on residue classes with a finite exception table.
The proof gives every branch, including the empty-word cases.

Such arithmetic data decide the word problem of the whole shell group.
For an input word, compute its finitely many candidate singular points.
If any is moved, the word is nonidentity. Otherwise normalize the germs
at those points using prefix transporters and compose their residue-affine
maps exactly. Identity germs yield explicit clopen neighborhoods on which
the word is identity. On the compact complement, every letter is an
effectively known prefix map on finitely many pieces; a finite table
calculation completes the decision.

Thus the specified E_nu is a finitely generated, decidable, simple group
containing A_5*A_5. It is not rational in this action. The separate node
`a5-arithmetic-shell-envelope-is-finitely-presented` retains the unresolved
finite-presentation question for this exact enumeration. A negative answer
would not refute the universal route, which may choose a different nu.

This is a test class for relation methods, not a universal input encoding.
Fixed residue-affine regular generator maps already give the input P a
polynomial-time word problem: evaluating a word at 0 uses integers whose
bit length grows linearly in word length. No such complexity restriction
is available for arbitrary decidable inputs. The universal presentation
problem remains intact.

## Verification boundary

These are written proofs in Cairn. Structural validation checks their
dependencies, not the mathematical arguments themselves. No GPU ran,
no local code or build was executed, and no Civo resource was created.
No finite presentation of the perfect-input shell benchmark is claimed.
