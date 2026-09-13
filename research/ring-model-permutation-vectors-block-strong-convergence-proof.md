---
rg: 2
id: ring-model-permutation-vectors-block-strong-convergence-proof
kind: route
title: Kesten norm below one against an exactly invariant column vector in the finite models
target: ring-model-permutation-vectors-block-strong-convergence
requires: []
artifacts:
  - research/artifacts/un-reduced-cstar-2026-09-13-part1.md
---

Artifact §2.3, Proposition 7 and its application.

1. **General firewall.** `‖V_i(h_K)‖ ≥ Re⟨V_i(h_K)ξ_i, ξ_i⟩ → 1`. The restriction of `λ_Γ` to `P_0` is a multiple
   of `λ_{P_0}` (cosets of `P_0`), so `‖λ_Γ(h_K)‖ = ‖λ_{P_0}(h_K)‖`. That is `< 1` by Kesten's criterion, since
   `P_0` is non-amenable. Strong convergence would force `‖V_i(h_K)‖ → ‖λ_Γ(h_K)‖ < 1`.
2. **Invariant column.** If `p ∈ G` fixes `e_1 ∈ R^n`, its first column is `e_1`. Applying `σ_i` entrywise inside
   the window gives an element of `GL_n(M_{N_i}(F_i))` whose first column is `c_i`, so `σ_i(p)c_i = c_i` exactly.
3. **A nontrivial vector.** The orbit `F_i c_i` carries the permutation module `ℓ²(F_i/H_i) ⊆ ℓ²(F_i)`, with
   `H_i = Stab(c_i)`, embedded as right-`H_i`-invariant functions.
   - Its constants are the constants of `ℓ²(F_i)`.
   - Put `ξ_i = (δ_{c_i} − |F_i c_i|^{-1}𝟙)/‖·‖`. It lies in `ℓ²_0(F_i)` and is exactly invariant under `σ_i(p)`
     for `p` as in step 2.
   - `F_i c_i ⊇ {σ_i(e_{21}(r))c_i : r in the window}`, which has at least `|σ_i(window)| → ∞` points, so the
     normalization stays bounded.
   - Any `π_i` containing this module contains `ξ_i`, so step 1 applies with `K ⊆ Stab_G(e_1) ∩ window`.
4. **Quotient by the centre.** `P_0` lies in the lower-right block, so it meets the scalars `Z(G)` trivially and
   maps isomorphically to `G/Z`. Use the orbit of the line `F_i^× c_i` instead of `c_i`.
5. **Non-amenable stabilizers.**
   - For `n ≥ 4`: `EL_{n−1}(R)` on coordinates `2,…,n` fixes `e_1`. It is infinite and Kazhdan by
     Ershov–Jaikin-Zapirain, since `R` is finitely generated, hence non-amenable.
   - For Pestov's ring with `n = 3`: the shift unit `u` spans `F_q[u] ≅ F_q[t]` (normal form of the crossed
     product). `E_2(F_q[t]) = SL_2(F_q[t])` (Euclidean ring) contains a free subgroup of rank 2 (Nagao's amalgam,
     recalled). Take `K` generating it.
