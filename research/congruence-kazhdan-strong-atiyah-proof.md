---
rg: 2
id: congruence-kazhdan-strong-atiyah-proof
kind: route
title: Gamma(3) lies in the 3-adic congruence kernel CS(1,3,3), and has property (T) as a lattice
target: congruence-kazhdan-groups-satisfy-strong-atiyah
requires:
  - p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah
---

**Torsion-free and infinite.** `Gamma(3)` has finite index in `SL_3(Z)`, so it
is infinite. It is torsion-free by Minkowski: a nontrivial element of finite
order congruent to `I` modulo an odd prime does not exist in `GL_d(Z)`.
Equivalently, `CS(1,3,3) = I + 3 M_3(Z_3)` is torsion-free.

**Property (T).** `SL_3(Z)` has property (T) (Kazhdan 1967, quoted in
arXiv:2606.19606 Section 1), and (T) passes to finite-index subgroups. So
`Gamma(3)` and its finite-index subgroups have (T). `E_3(3)` has finite index in
`SL_3(Z)`, since `E_3(q)` has finite index for `d >= 3` (Bass--Milnor--Serre).
It is the explicit host of the `e33-*` nodes.

**Strong Atiyah and domains.** Reduction of entries gives
`Gamma(3) <= CS(1,3,3) = {A in Mat_3(Z_3) : A = I mod 3}`. By
[[p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah]], every subgroup of
`CS(1,3,3)` satisfies Strong Atiyah over `C`, and its group ring over any field
of characteristic `0` or `3` is a domain.

For `Gamma(p) <= CS(1,d,p)` with `p` odd, and `Gamma(4) <= CS(2,d,2)`, the
argument is identical.
