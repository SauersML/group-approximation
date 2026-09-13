---
rg: 2
id: lef-kazhdan-group-without-finite-quotients-exists-proof
kind: route
title: Elementary matrices over a simple LEF ring are Kazhdan, LEF, and have only the level-ideal finite quotients
target: lef-kazhdan-group-without-finite-quotients-exists
requires: [minimal-subshift-algebra-is-simple-lef-ring, elementary-groups-over-fg-rings-have-property-t, lef-implies-operator-mf]
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
---

Put `G = EL_3(R)`.

- **Kazhdan.** `R` is finitely generated with 1 (`minimal-subshift-algebra-is-simple-lef-ring`,
  item 1), so `G` has property (T) by `elementary-groups-over-fg-rings-have-property-t`.
- **LEF and MF.** `R` embeds unitally in `prod_omega M_(N_k)(F_q)` (item 3), so
  `G <= GL_3(R) <= prod_omega GL_(3N_k)(F_q)`. A finitely generated subgroup of an algebraic
  ultraproduct of finite groups is LEF. It is then operator MF by `lef-implies-operator-mf`.
- **Infinite.** `e_12(LC(X,F_q)) <= G`.
- **No finite quotients.** Let `N ⊴ G` have finite index. The level set
  `I(N) = {a : e_12(a) ∈ N}` is a two-sided ideal: it is additive, and
  `[e_12(a), e_23(b)] = e_13(ab)` and `[e_31(b), e_12(a)] = e_32(ba)`, with signed permutation
  matrices in `G` moving roots between positions. `e_12(R) ∩ N = e_12(I(N))` has finite index in
  `e_12(R) ≅ (R,+)`, and `R` is infinite, so `I(N) != 0`. `R` is simple (item 2), so `I(N) = R`.
  Then every root lies in `N` and `N = G`.

Refutation of `mf-kazhdan-group-without-finite-quotients-is-trivial`: `G` is a nontrivial operator-MF
Kazhdan group whose homomorphisms to finite groups are all trivial.
