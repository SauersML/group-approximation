---
rg: 2
id: el-rank-four-finite-simple-shadows-are-ring-models-proof
kind: route
title: Finitely presented Steinberg cover, level ideal, central K_2, nilpotent radical kernel, one simple factor
target: el-rank-four-finite-simple-shadows-are-ring-models
requires: [steinberg-finite-presentation-and-kazhdan-theorem, semilocal-steinberg-groups-have-central-k2]
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part4.md
---

Full proof: artifact part 4 §1, steps 1–7.
- **Cover.** `St_N(F)` is finitely presented on `x_ij(1)`, `x_ij(t_m)`. Its relators are relators of `G`, hence of `Q_k`
  for large `k`, so `ψ_k: St_N(F) → Q_k` exists.
- **Level ideal.** The inclusion cycle and `[x_ij(a), x_jl(b)] = x_il(ab)` give one two-sided ideal `K`, as in
  `lef-elementary-groups-force-lef-rings-proof` step 4. `F/K ↪ Q_k` additively, so `A_k = F/K` is finite, and `ψ_k`
  factors through `St_N(A_k)`.
- **Central kernel.** `K_2(N,A_k)` is central, and a central normal subgroup of a nonabelian simple group is trivial.
  So `Q_k` is a quotient of `E_N(A_k)`.
- **Radical.** `ker(E_N(A_k) → E_N(A_k/J)) ⊆ I + M_N(J)` is nilpotent, so it dies in `Q_k`.
- **Semisimple part.**
  - `A_k/J = ∏ M_(d_i)(F_(q_i))` and `E_N(A_k/J) = ∏ SL_(N d_i)(F_(q_i))`, a product of perfect quasisimple groups.
  - The images of the factors are normal and commute, so one factor surjects and the center dies. Hence
    `Q_k ≅ PSL_(Nd)(F_q)`, with `ρ_k` the composite `F → A_k → M_d(F_q)`.
- **Relations of R.** A relation `p ∈ ker π` gives the relator `e_12(π p) = 1` of bounded length, so `e_12(ρ_k p)` is
  central and `ρ_k(p) = 0`.
