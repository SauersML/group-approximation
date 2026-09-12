---
rg: 2
id: sl3z-strong-atiyah-via-iwahori-index-8
kind: route
title: A torsion-free index-168 subgroup of SL_3(Z_2) and Gamma(3) together force denominator 24
target: sl3z-satisfies-strong-atiyah
requires:
  - sl3-z2-iwahori-has-torsion-free-subgroup-of-index-8
  - p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah
---

Let `W <= I <= SL_3(Z_2)` be torsion-free of index 8 in `I`, so
`[SL_3(Z_2) : W] = 168 = 2^3 * 3 * 7`. Put `H_2 = W cap SL_3(Z)`.
- `SL_3(Z)` is dense in `SL_3(Z_2)`, since reduction mod `2^j` is surjective. So
  `[SL_3(Z) : H_2] = 168`.
- `W` is a torsion-free compact 2-adic analytic group. By
  [[p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah]], its subgroup
  `H_2` satisfies Strong Atiyah over `C`.
- `H_3 = Gamma(3)` has index 5616 and satisfies Strong Atiyah over `C`, by the
  same claim.

For `A` over `C[SL_3(Z)]`, `rk(A) = rk_{H_j}(res A)/[G:H_j]` lies in
`(1/168)Z cap (1/5616)Z = (1/24)Z`, since `gcd(168, 5616) = 24`.

The route also records the converse direction of the reduction. Every
torsion-free open `W <= SL_3(Z_2)` whose index has 2-adic valuation 3 is
conjugate into `I` with index 8. Its image in `SL_3(F_2)` has no elements of order
3 or 7: the closure of a cyclic subgroup contains its prime-to-2 torsion part.
