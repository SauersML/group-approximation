---
rg: 2
id: sl4z-reduced-not-mf-from-corona-block-sl2-norm-four
kind: route
title: Norm four in every corona representation makes the reduced C-star algebra of SL_4(Z) and of each overgroup non-MF
target: sl4z-reduced-cstar-is-not-mf
requires: [sl4z-corona-representations-have-block-sl2-norm-four]
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13.md
---

Artifact, Section 4, Theorem 1.  Let `Gamma >= SL_4(Z)`, and suppose
`iota : C*_r(Gamma) -> Q_k = prod_n M_(k_n) / sum_n M_(k_n)` is injective.  Take
`Gamma = SL_4(Z)` for the root.

1. **Make it unital.**  Lift the projection `iota(1)` to projections `P_n` of rank `r_n`.
   Corner by it to get a unital injective `iota : C*_r(Gamma) -> Q_r != 0`.
2. **Apply the claim.**  `pi = iota o lambda_Gamma`, restricted to `C*(SL_4(Z))`, is a
   unital *-homomorphism into `Q_r`.  By `sl4z-corona-representations-have-block-sl2-norm-four`,
   `||pi(S + S^-1 + T + T^-1)|| = 4`.
3. **Compare with the regular norm.**  `iota` is isometric, so this equals
   `||lambda_Gamma(S + S^-1 + T + T^-1)||`.  `lambda_Gamma|_(SL_2(Z))` is a multiple of
   `lambda_(SL_2(Z))`, and `SL_2(Z)` is nonamenable, so Kesten gives `< 4`.
   Contradiction.
