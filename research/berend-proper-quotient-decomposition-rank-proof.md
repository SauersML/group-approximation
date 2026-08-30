---
rg: 2
id: berend-proper-quotient-decomposition-rank-proof
kind: route
title: Reduce a proper quotient to finite orbit groupoids and rank-two stabilizer tori
target: berend-proper-quotients-have-decomposition-rank-at-most-two
requires:
  - berend-torus-actions-give-strongly-qd-polycyclic-groups
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Write `X = T^3` and `Gamma = Z^2`.  The action is topologically free, so
the ideal-intersection theorem used by Archbold--Spielberg gives

`I cap C(X) != 0`                                               `(BPP1)`

for every nonzero ideal `I` of `A`.  Let `U` be the nonempty invariant
open subset corresponding to `I cap C(X)`, and set `F = X \ U`.  Exactness
of the amenable group `Gamma` gives a surjection

`C(F) ⋊ Gamma -> A/I`.                                      `(BPP2)`

The Berend invariant-set property used in Eckhardt's Lemma 2.2 says that
every proper closed invariant subset of `X` is finite.  Hence `F` is a
finite disjoint union of finite orbits `O_1,...,O_s`.

For a finite transitive orbit `O`, choose `x in O` and let
`H = Stab_Gamma(x)`.  The finite transitive transformation groupoid is a
matrix groupoid over its isotropy, so

`C(O) ⋊ Gamma = M_{|O|}(C*(H))`.                             `(BPP3)`

The subgroup `H` has finite index in `Gamma = Z^2`, and therefore
`H = Z^2` abstractly and `C*(H) = C(T^2)`.  Decomposing `F` into orbits
proves `(BPQ2)`.

Every quotient of a finite direct sum of matrix algebras over `C(T^2)` is
a finite direct sum of algebras `M_n(C(Y))` for closed subsets
`Y subseteq T^2`.  Decomposition rank is invariant under matrices and
equals covering dimension on commutative algebras.  Since `dim(Y) <= 2`,
`(BPQ1)` follows.
