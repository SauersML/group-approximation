---
rg: 2
id: raag-skew-field-betti-numbers-of-finite-index-subgroups
kind: claim
title: Over any division ring containing its group algebra, a finite-index subgroup of a right-angled Artin group has Betti numbers equal to the index times the shifted reduced Betti numbers of the flag complex
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md
---

Let `L` be a finite nonempty flag complex, `A_L` its right-angled Artin group, `H ≤ A_L`
a subgroup of finite index, `F` a field, and `D` any division ring containing `F[H]`
as a subring. Then for every `p ≥ 0`

`H_p(H; D) ≅ D^{[A_L:H] · b̃_{p−1}(L; F)}`,

where `b̃_j(L; F) = dim_F H̃_j(L; F)`.

The number does not depend on `D`, and in particular not on any character of `H`.
For `F = Q`, `H = A_L` and the Linnell division ring this is the Davis--Leary formula
for ℓ²-Betti numbers.

Proof: artifact part 1, Theorem 1 (Mayer--Vietoris over the cover of the finite
cover of the Salvetti complex by lifted maximal tori; the tori are `D`-acyclic by a
Koszul argument, and only the vertices contribute, through the nerve of the maximal
simplices of `L`).
