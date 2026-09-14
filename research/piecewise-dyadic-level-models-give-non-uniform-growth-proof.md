---
rg: 2
id: piecewise-dyadic-level-models-give-non-uniform-growth-proof
kind: route
title: Partial translations give dyadic matrix units, the corner is an induced crossed product, Krieger recodes it binary, and the small-ball engine applies
target: piecewise-dyadic-level-models-give-non-uniform-growth
requires: [el-small-ball-generating-sets-from-grigorchuk-levels, ejz-elementary-groups-explicit-kazhdan-constant, krieger-subshift-embedding-theorem]
artifacts:
  - research/artifacts/sk-growth-gx-sturmian-2026-09-14-part1.md
---

Notation: `R = R_X = LC(X,F_2) ⋊_T Z`, `(fu^i)(f′u^j) = f(f′∘T^(−i))u^(i+j)`, so `u^j e_U u^(−j) = e_(T^jU)`. Full details in artifact part 1 §2.

1. **Dyadic matrix units.** For a piecewise level model at scale `k`, put `s_i = Σ_n u^n e_(A^(i)_n)` and `s′_i = Σ_n e_(A^(i)_n) u^(−n)`.
   - Cross terms `e_(A_m ∩ T^(n−m)A_n)u^(n−m)` vanish for `m ≠ n` because the images `T^nA_n` are disjoint, so `s′_i s_i = e_(W_1)` and `s_i s′_i = e_(W_i)`.
   - `s′_j = s′_j e_(W_j)` and `s_i = e_(W_i)s_i` give `s′_j s_i = 0` for `j ≠ i`.
   - So `ε_ij = s_i s′_j` are matrix units with `Σ_i ε_ii = 1`, and `R ≅ M_(2^k)(A_k)` with `A_k = e_(W_1) R e_(W_1)`.
2. **The corner is an induced crossed product.**
   - `e_W(fu^j)e_W = f 1_(W∩T^jW) u^j`. With return time `r: W → Z_(>0)` (bounded, by minimality and compactness), `B_j = {r = j}` and `v = Σ_j e_(T^jB_j) u^j`, the element `v` is a unit of the corner with inverse `Σ_j u^(−j) e_(T^jB_j)`.
   - Every `f1_(W∩T^jW)u^j` is `Σ_m f 1_(C_m) v^m`, with `C_m` the clopen set of points whose length-`|j|` orbit segment meets `W` in the right number of places.
   - So `A_k ≅ LC(W_1,F_2) ⋊_(T_W) Z` for the first-return map `T_W`.
3. **Bounded generation.**
   - `(W_1, T_W)` is conjugate to a subshift over the finite alphabet of return words, since a point of a subshift is determined by its coordinates along the orbit. It is minimal and infinite, so aperiodic.
   - Its entropy is `sup_ν h_ν(T_W) = sup_μ h_μ(T)/μ(W_1) = 0` (Abramov and the variational principle).
   - By `krieger-subshift-embedding-theorem` it embeds into `{0,1}^Z`. So some clopen `U ⊆ W_1` has `T_W`-translates separating points, and `A_k` is generated as a ring by `Σ_k = {v, v^(−1), e_U}`, with `|Σ_k| = 3` for all `k`.
4. **Engine.**
   - `EL_3(R) ≅ EL_3(M_(2^k)(A_k)) = EL_(3·2^k)(A_k) = EL_(Y_k)(A_k)` (artifact sk-free-8 part 2 Lemma 4).
   - The generating sets `T_k(Σ_k)` of `el-small-ball-generating-sets-from-grigorchuk-levels` satisfy `γ(ℓ) ≤ exp(Cℓ^β)` for `ℓ ≤ 2^(⌊k/2⌋)/3`, with `C,β` depending only on `|Σ_k| = 3` and `m = 3`.
   - Lemma 0 of sk-free-8 part 1 gives `ω(G_X, U_k) ≤ exp(C(2^(⌊k/2⌋)/3)^(β−1)) → 1` along the good scales.
5. **Exponential growth.** `G_X` is infinite and has property (T) (`ejz-elementary-groups-explicit-kazhdan-constant`), hence is non-amenable. Groups of subexponential growth are amenable, so `ω(G_X,S) > 1` for every `S`. ∎
