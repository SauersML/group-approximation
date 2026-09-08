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

## Next necessary presentation test

The one-singularity subgroup A_1 maps onto the entire isotropy germ
group Q=(E_nu)_p. Its kernel K consists of maps equal to the identity
near p. Because A_1 is locally V away from p, such a kernel element
is locally V everywhere and hence belongs to V. Therefore

    K = union_(n>=1) Fix_V(0^n*C).

Each group in this nested union is isomorphic to the simple group V:
its complementary clopen set is a finite union of binary cones and
admits a finite prefix identification with the full binary Cantor
set. A nested union of nontrivial simple groups is simple. Indeed
a nontrivial normal subgroup meets some stage nontrivially, and
then contains every larger stage by simplicity. Thus K is simple.

In particular any nonidentity k in K normally generates K inside
A_1. If A_1 is finitely presented, its quotient Q is finitely
presented by adding the single relator k=1. This is an instance of
`fp-quotient-iff-kernel-finitely-normally-generated`.

Hence a candidate enumeration must first yield a finitely presented
near-permutation group Q. This is only a necessary test: finite
presentation of Q does not, by itself, provide a finite presentation
of A_1 or either of the two-point subgroups. In particular the
non-finitely-generated neighborhood kernel cannot be ignored when
trying to lift relations back from germs. The earlier commuting
boundary lamps act on the interiors of shells; they are not the
suffix-preserving shell permutations used in the near-index
obstruction, so that obstruction does not contradict their proof.

## Verification boundary

These are written mathematical arguments and source imports in Cairn.
No GPU computation or new Lean formalization establishes them.

The complexity proof is commit `383d99e42` and the universal shell
route is commit `87b76b59a`. The first remote attempt was stopped
by a pre-existing overlong exterior-injection proof ID. Commit
`b58263c36` shortened that ID and its filename without changing its
mathematical contents.

[Research run 34292617383](https://github.com/SauersML/group-approximation/actions/runs/34292617383)
completed successfully at main integration
`0c5fcc81ef748a420cf6e819c9b05332fd00569d`. Downloaded evidence is
retained in `.cairn/bh-shell-germ-check-20260908/`.

The inspected `node_status` fields are ESTABLISHED for the rational
word-problem bound, the resulting nonembedding claim, the universal
shell realization, and the prefix-germ obstruction. They are OPEN
for `decidable-inputs-have-fp-shell-stabilizers`, its Boone--Higman
route, and `boone-higman-conjecture`. Existing source-syntax checks
and finite controls also passed. This validates dependency wiring
and finite controls, not the infinite-group proofs. The necessary
presentation test above is additional proof text in this artifact;
it has not been promoted to a separately checked theorem.
