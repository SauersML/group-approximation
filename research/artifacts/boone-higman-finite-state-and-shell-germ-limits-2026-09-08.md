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

## Verification boundary

These are written mathematical arguments and source imports in Cairn.
No GPU computation or new Lean formalization establishes them. Remote
graph validation will be recorded after integration.
