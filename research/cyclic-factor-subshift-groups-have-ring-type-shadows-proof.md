---
rg: 2
id: cyclic-factor-subshift-groups-have-ring-type-shadows-proof
kind: route
title: Rewrite G_X as EL_3m over the induced subshift and apply rank-four type rigidity after a change of marking
target: cyclic-factor-subshift-groups-have-ring-type-shadows
requires: [tower-subshift-elementary-group-is-el-3k-of-base, cyclic-factor-subshift-el-2-is-simple-kazhdan-lef, el-rank-four-finite-simple-shadows-are-ring-models, rank-four-subshift-groups-see-rational-spectrum]
artifacts:
  - research/artifacts/sk-rank3-shadows-2026-09-14.md
---

Full proof: artifact §3.
1. The cyclic piece gives `R_X ≅ M_m(R_(X_1))` and `G_X = EL_(3m)(R_(X_1))`, with `3m ≥ 6` and `X_1` an infinite minimal
   subshift (tower and cyclic-factor nodes).
2. A change of finite marking preserves converging sequences (Theorem E, invariance of `Div`). So `(Q_k, T′_k)` converges
   to `EL_(3m)(R_(X_1))` with its elementary marking.
3. Theorem D with `N = 3m ≥ 4` gives `Q_k ≅ PSL_(3md_k)(F_(q_k))`, induced by surjective ring maps `ρ_k: F_1 → M_(d_k)(F_(q_k))`,
   and `d_k → ∞` because `EL_(3m)(R_(X_1))` is infinite and simple.
4. `2 ∈ ker(F_1 → R_(X_1))` is killed eventually (Theorem D, item 6), so `q_k` is a power of 2.
5. Divisibility by `3m c`, `c ∈ Cyc(X_1)`: Theorem E ⊇ for `X_1`. ∎
