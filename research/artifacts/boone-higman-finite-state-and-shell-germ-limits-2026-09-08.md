# Finite-state bounds and the unrestricted shell-germ route

The boundary-wreath construction does not become universal simply by
dropping contraction while retaining finite-state Cantor generators.
There are decidable finitely presented residually finite groups which
embed in no rational homeomorphism group at all. Cairn records this
as `decidable-fp-groups-need-not-embed-in-rational-group`.

## The quantitative obstruction

The proof `rational-transducer-cascade-and-delay-proof` composes a
word of length n into a cascade with at most s^n states and l^n
output letters per transition, for fixed s,l. A breadth-first check
assigns each state the unread portion of the input prefix. Equality
with the identity holds exactly when all transition equations and
all repeated-state residual words are consistent. Those residuals
have length at most the number of states. The resulting word-problem
algorithm runs in deterministic time 2^O(n).

The group supplied by the Kharlampovich--Myasnikov--Sapir hardness
theorem can be chosen to have no such algorithm. An abstract embedding
would fix a finite collection of image transducers and hence supply
the forbidden algorithm. Changing the alphabet, allowing large
transducers, or declining to compute the embedding does not avoid
this argument: those choices only change fixed constants.

The source and its quantitative definition of hardness are linked
in `kms-complexity-excludes-rational-embeddings-proof`. The argument
uses actual word-problem complexity, not a lower bound on the Dehn
function and not undecidability of the torsion problem.

## Consequence for the previous positive construction

The intermediate actor E in
`boundary-orbit-cyclic-wreath-germ-proof` is rational: contracting
coefficients are finite state, the recurring lamp has finitely many
states, and a finite prefix table with finite-state coefficients is
an asynchronous finite-state transducer. Thus the hard group above
cannot embed in any of those intermediate actors, even through an
embedding unrelated to their displayed wreath subgroups.

This strengthens the earlier residual-finiteness restriction on the
input wreath products. It does not establish the same restriction
for their final twisted Brin--Thompson envelopes: those envelopes
act on a different Cantor space, and no rational realization of
that action has been proved here. Nor does it exclude arbitrary
finite germ extensions with nonrational generators.

## A universal realization that survives that obstruction

An arbitrary enumeration nu:P->N puts the left regular action of
an infinite countable P on even-indexed binary shells 0^n*1*C,
fixing the odd shells and their common limit p=0^infinity. This
is a faithful Cantor action, with each nonidentity input element
singular only at p relative to V. The full generated group
E_nu=<V,hat(P)> is a finite germ extension with dense singular
orbit Omega=V*p. The complete construction and germ calculation
are in `shell-cantor-embedding-and-germ-proof`.

Its isotropy germ at p is the near-permutation subgroup generated
by the input permutations and the cofinite shift tau:n->n+1.
The prefix germ <tau> has infinite index and is not normal. Near
index forces any normalizing conjugation to fix tau, but an actual
permutation commuting with tau eventually is finitary. This
contradicts the input's free regular orbit. Finite index would make
the index-zero kernel finite, contradicting its embedded copy of P.

This explains why the convenient finite-index/normal-germ criterion
cannot make the universal shell construction finitely presented.
It does not refute the more general finite-germ theorem.

## The remaining construction is now three precise groups

`decidable-inputs-have-fp-shell-stabilizers` asks for an enumeration
for which three groups are finitely presented: elements singular
only at p and fixing p; elements singular only at p and fixing p,q;
and elements singular at most at p,q and fixing both. These are
global subgroups, not finite samples of singular behavior.

`boone-higman-via-shell-germ-stabilizers` proves that these clauses
would imply the full conjecture. The finite-germ theorem at n=2
gives finite presentation of E_nu. At n=1, applied to a point
stabilizer, the very same clauses give its finite generation.
The faithful dense-orbit action then meets the existing twisted
Brin--Thompson criterion. All clauses with no singular points are
already supplied by finite presentation of rational stabilizers in V.

The new shell-stabilizer claim remains OPEN. It is a different
construction problem from finite presentation of the Mallery--Zaremsky
permutation envelope on N; no equivalence is asserted. The input's
decidable word problem has not yet been converted into finite
presentations for these three groups. The conjecture remains OPEN.

## Verification boundary

These are written mathematical arguments and source imports in Cairn.
No GPU computation or new Lean formalization establishes them. Remote
graph validation will be recorded after integration.
