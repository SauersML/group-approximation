---
rg: 2
id: separable-ii1-factors-weakly-dense-popa-combs-proof
kind: route
title: Tensor teeth in a hyperfinite subfactor, approximants free on the no-tooth region and scheduled finite blocks on first-tooth regions, and separation through a universal RFD algebra
target: separable-ii1-factors-have-weakly-dense-popa-combs
requires:
  - li-shen-amalgamated-rfd-criterion
  - exel-loring-free-products-of-rfd-algebras-are-rfd
artifacts:
  - research/artifacts/sk-popa-input2-2026-09-14-part1.md
---

Complete derivation in the artifact, §§1–5. Summary:

1. **Setup.**
   - `R = (⊗_{i≥0}N_i)'' ⊆ M` unital, with `N_i ≅ M_{r_i}`, `Σ1/r_i < ∞`, and `p_i ∈ N_i` rank one.
   - `R_{k,m} = ∏_{k≤i'<m}(1−p_{i'})p_m` and `g_k = ∏_{i'≥k}(1−p_{i'})`.
   - `z_k = u_k + Σ_{m≥k}c_k^{(m)}`, with `u_k ∈ U(g_kMg_k)` the polar part of `g_ky'_kg_k`, and `c_k^{(m)} ∈ U(R_{k,m}(⊗_{i'≤m}N_{i'})R_{k,m})`.
   - `A_i = C*(N_{<i}, z_1..z_i)` and `e_i = p_i`.
2. **Commutation.** `z_k` commutes with `p_j` for `j ≥ k`: the regions are orthogonal to or inside `p_j`, or the blocks live on earlier tensor factors.
3. **(C1).** `z_kp_j = Σ_{m≤j}c_k^{(m)}p_j ∈ (⊗_{i'<j}N_{i'})p_j`. So `e_jA_je_j = (⊗_{i'<j}N_{i'})p_j`, a full matrix algebra.
4. **(C3).** The matrix units of `N_i` sum the translates of `p_i` to 1.
5. **Weak density.** `‖z_k − y'_k‖_2 ≤ 4τ(1−g_k)^{1/2} ≤ 4(Σ_{i'≥k}1/r_{i'})^{1/2} → 0`.
6. **`W_i`.** In `A_i`, `z_k = f_k + v_k` with `f_k ∈ M_{D_i}` and `v_k` a unitary on `b_k = ∏_{k≤i'<i}(1−p_{i'})`. `W_i := C*⟨M_{D_i}, v_k : v_k^*v_k = v_kv_k^* = b_k⟩` is an iterated amalgamated free product over `C²`. It is RFD by Li–Shen with compatible multiplicity embeddings, and by Exel–Loring when `b_k = 1`.
7. **(C2).** Schedule `m ↦ (i,n)` with `i ≤ m` and `∏_{i≤i'<m}(r_{i'}−1) ≥ t^{(i)}_n`. Put the `n`-th separating representation of `W_i` into `c_k^{(m)} = (ρ(v_k) ⊕ 1) ⊗ 1` on `b_kC^{D_i} ⊗ E_m`.
   - The compression to `Q = ∏_{i≤i'<m}(1−p_{i'})p_m ≤ e_m` contains `ρ^{(i)}_n` as a subrepresentation.
   - So `‖w‖_{W_i} ≤ sup_{m≥i}‖q(w)e_m‖`. Hence `A_i ≅ W_i` and the teeth separate points.
8. **Conclusion.** (C1)–(C3) hold and `A'' = M`.
