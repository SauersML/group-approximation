---
rg: 2
id: approximation-property-recognition-dichotomy-proof
kind: route
title: Side A is trivial and side B is the second-level Rice theorem
target: approximation-property-recognition-dichotomy
requires:
  - second-level-rice-theorem-for-local-approximation-properties
  - local-approximation-properties-are-marked-closed
  - nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound
---

Hyperlinearity is a local approximation property (model predicate: unitary
models in normalized Hilbert--Schmidt distance, `Sofic.IsHyperlinear`), and
residually finite groups are sofic hence hyperlinear
([[sofic-implies-hyperlinear]]), so (H1) holds.

**(A)**  If every group is hyperlinear, each of the three sets is the set of
all codes, which is decidable.

**(B)**  If some group `G` fails hyperlinearity, then some finitely generated
subgroup of `G` fails it (locality, clause 2 of
[[local-approximation-properties-are-marked-closed]]), so (H2) holds and
[[second-level-rice-theorem-for-local-approximation-properties]] applies:
clauses (a)--(c) give the hardness statements, and clause (d) with the
upper bound [[nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound]]
(with a relator prefix in the certificate for recursive presentations) gives
the completeness and strict-interval statements.

**(D2).**  (i) => (ii) is clause 4 of
[[local-approximation-properties-are-marked-closed]]; (ii) => (i) is trivial.
(i) => (iii), (iv), (v), (vi) are side (B).  Each of (iii), (iv), (vi)
implies that `HYP` is not the full set, i.e. (i); (v) implies (iv) because a
`Pi^0_2`-complete set is not decidable.

The hyperlinear finite-presentation core of this paragraph is now formal:
`Covers/HyperlinearTableCover` proves `(i) <=> (ii)` (including the
universe-polymorphic finitely generated extraction), and
`Computability/HyperlinearMarkov` proves `(i) <=> (iii)` by constructing the
general Adian--Rabin reduction from the forbidden table code.  Its converse
installs the constant-true decision procedure under `not (i)`.

**Other properties.**  Weakly sofic and linear sofic groups are defined by
table models in finite groups with bi-invariant metrics, respectively in
`GL_n` of a field with the normalized rank metric, so both are local
approximation properties, and both contain the sofic groups (Hamming is
bi-invariant; permutation matrices realize Hamming distance as rank distance
up to a constant).  Hence (H1) holds and the same two sides are exhaustive.
Only the placement in `Pi^0_2` is not recorded here, so side (B) reads
"`Pi^0_2`-hard" for them.
