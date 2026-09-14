---
rg: 2
id: subshift-el-reduced-not-mf-from-laurent-corona-norm-four
kind: route
title: Norm four in every corona representation of the Laurent lattice makes C*_r(G_X) non-MF
target: subshift-elementary-group-reduced-cstar-is-not-mf
requires:
  - laurent-sl4-corona-representations-have-block-sl2-norm-four
  - subshift-elementary-groups-contain-laurent-sl-n-lattices
  - ring-model-permutation-vectors-block-strong-convergence
artifacts:
  - research/artifacts/sk-mf-laurent-2026-09-14-part1.md
---

Artifact part 1, Section 5.

1. **The lattice inside G_X.** By `subshift-elementary-groups-contain-laurent-sl-n-lattices` with `k = 2`,
   `SL_6(F_q[t^{±1}]) ≤ G_X`, and its upper-left block is `Λ = SL_4(F_q[t^{±1}])`.
2. **Restrict and make unital.** Suppose `ι : C*_r(G_X) → Q = ∏_n M_{k_n}/⊕_n M_{k_n}` is injective.
   - `λ_{G_X}|_Λ` is a multiple of `λ_Λ`, so `ι` restricts isometrically to `C*_r(Λ)`.
   - Lift the projection `ι(1)` to projections of rank `r_n`, and corner to get a unital injective map into
     `Q_r ≠ 0`.
3. **Apply the crux.** `π = ι∘λ_Λ : C*(Λ) → Q_r` is unital, so `‖π(z)‖ = 4` by
   `laurent-sl4-corona-representations-have-block-sl2-norm-four`.
4. **Compare with the regular norm.** `ι` is isometric, so `‖π(z)‖ = ‖λ_Λ(z)‖`. `S, T` are free (Nagao; item 3 of
   `ring-model-permutation-vectors-block-strong-convergence`), so `λ_Λ` restricted to `⟨S,T⟩` is a multiple of
   `λ_{F_2}`, and Kesten gives `2√3 < 4`. Contradiction.
