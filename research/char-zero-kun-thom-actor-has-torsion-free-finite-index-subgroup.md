---
rg: 2
id: char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup
kind: claim
title: Characteristic-zero Kun--Thom-type actors have torsion-free finite-index subgroups with trivial word problem
distinct_from:
  kun-thom-actors-have-no-torsion-free-finite-index-subgroups: that shows the positive-characteristic Theorem E actors are not virtually torsion-free; this shows the characteristic-zero analogues are, with an explicit subgroup.
---

**ESTABLISHED.** Setup:
- Let `r >= 2`, `d >= 1`, and `R = Z[x_1^(+-1),...,x_d^(+-1)]`.
- Let `G_0 = EL_r(R) semidirect SL_d(Z)`, where `A` in `SL_d(Z)` acts entrywise
  by the monomial substitution `x^v -> x^(Av)`.
- For a prime `p >= 3`, let
  - `K = ker(EL_r(R) -> GL_r(F_p))`: evaluate `x_i -> 1`, then reduce mod `p`;
  - `Gamma_d(p) = ker(SL_d(Z) -> SL_d(F_p))`.

Then `H = K semidirect Gamma_d(p)` is a torsion-free subgroup of finite index
in `G_0`. Elements are pairs `(M, A)` of a Laurent-polynomial matrix and an
integer matrix, multiplied as `(M,A)(M',A') = (M alpha_A(M'), AA')`, so
equality is entrywise and the word problem is trivial.

For `kaplansky-zero-divisor-conjecture` (and for Strong Atiyah), these give
admissible torsion-free hosts with exact multiplication, built from the same
actor shape as the Kun--Thom pairs.

Caveats: whether Kun--Thom Theorems A and E hold for these
characteristic-zero pairs is not checked here, and `G_0` is residually
finite, hence sofic.

Derivation supplied by the `atiyah-nonsofic` lane and checked by
`zero-divisor-tf`.
