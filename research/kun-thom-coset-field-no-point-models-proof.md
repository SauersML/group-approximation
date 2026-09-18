---
rg: 2
id: kun-thom-coset-field-no-point-models-proof
kind: route
title: Hash the point values to bits, tensor with a sofic approximation, pass to finite models of the coset shift, and let Theorem C collapse the disagreement a unit denominator forces
target: kun-thom-coset-field-has-no-finite-field-point-models
requires:
  - finite-field-point-models-give-the-rank-condition
  - kun-thom-nonsofic-wreath
  - sofic-action-with-sofic-ergodic-components-is-sofic
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-2026-09-12.md
---

Write `x_c = x_(c,1)`, `(gω)(c) = ω(g^{-1}c)` on `X = {0,1}^H` and `(g·f)(ω) = f(g^{-1}ω)`. Lemma LC is Section 2 of
the artifact, used inside the proof of `sofic-action-with-sofic-ergodic-components-is-sofic`. Theorem C is
imported in `kun-thom-nonsofic-wreath`.

0. **The pair.** Since `Γ` is not normal, some `g` has `g^{-1}Γg ⊄ Γ`. If `g_0Γg_0^{-1} ⊄ Γ`, take `g = g_0^{-1}`.
   Otherwise `g_0Γg_0^{-1} ⊊ Γ`, and `g = g_0` works. Pick `γ ∈ Γ` with `g^{-1}γg ∉ Γ`, and put `c = gΓ`,
   `c' = γc ≠ c`, `δ = x_c - x_(c')`. `δ ≠ 0` in the field, so `δ^(-1) ∈ K_H(k)`.
1. **Models.** Suppose point models exist. Choose finite `H_n ↑ H` with `c, c' ∈ H_n`, finite `W_n ↑ G`, and
   `ε_n → 0`. Let `E_n = {x_d : d ∈ H_n} ∪ {δ, δ^(-1)}`, and take a model `(V_n, F_n, σ_n, e, V_n^good)` for
   `(E_n, W_n, ε_n)`.
2. **Nonvanishing.** Let `v ∈ V_n^good`. By (P1) with `h = e`, `E_n ⊆ O_v`. `e_v` is a unital ring homomorphism,
   so `e_v(δ)e_v(δ^(-1)) = 1` and `e_v(x_c) ≠ e_v(x_(c'))`.
3. **Hash.** A uniformly random map `F_n -> {0,1}` separates two distinct values with probability `1/2`. Fix
   `h_n` separating `e_v(x_c), e_v(x_(c'))` for at least half of `V_n^good`. Put `Ω_v(d) = h_n(e_v(x_d))` if
   `x_d ∈ O_v`, and `0` otherwise, so `Ω_v ∈ X`.
4. **Approximate equivariance.** Let `v` be good, `h ∈ W_n` and `x_d ∈ E_n`. (P1) puts `x_d` in
   `O_(σ(h)^(-1)v)` and `x_(hd) = σ_h x_d` in `O_v`. (P2) gives `e_(σ(h)^(-1)v)(x_d) = e_v(x_(hd))`. So
   `Ω_(σ(h)^(-1)v)(d) = Ω_v(hd) = (h^{-1}Ω_v)(d)` for all `d ∈ H_n`.
5. **Tensor.** Let `s_n : G -> Sym(S_n)` be a sofic approximation (`G` is sofic). Put `Y_n = V_n × S_n`,
   `τ_n(h) = σ_n(h) × s_n(h)`, and `Ω_(v,s) = Ω_v`. Let `ν_n` be the law of `Ω_y` for uniform `y ∈ Y_n`, and `μ`
   its weak-* limit along a free ultrafilter `U`. `X` is compact and cylinders are clopen, so
   `μ(B) = lim_U ν_n(B)` for every cylinder `B`.
   - **Invariance.** For a cylinder `B` on coordinates in `H_n ∩ h^{-1}H_n`, step 4 and the bijectivity of
     `σ_n(h)` give `|ν_n(hB) - ν_n(B)| <= 2ε_n`. So `μ` is `G`-invariant.
   - **Disagreement.** By step 3, `μ(ω(c) ≠ ω(c')) >= lim (1 - ε_n)/2 = 1/2`.
6. **Soficity (Lemma LC).**
   - Use the cylinder partitions `P_j` on the first `j` cosets of an enumeration, and let `F_j ↑ G`.
   - A word `w` of level `j` rewrites as `1_(B_w) u_(h_w)` in the crossed product. In `Y_n`, the same rewriting
     is exact at every `y = (v,s)` such that the `<= j` points `σ_n(prefix)^(±1) v` are good and the `<= j`
     products of `s_n` along the word are exact at `s`.
   - This holds for a fraction `>= 1 - 2jε_n - o(1)` of `y`, by step 4 and (P3), since `B_w` is a cylinder on
     coordinates in `H_n` for large `n`.
   - Then `tr(w on Y_n)` is `ν_n(B_w) + o(1)` if `h_w = 1`, and at most `tr(s_n(h_w)) + o(1) -> 0` otherwise.
     Along `U` this is `τ(w)`.
   - So models of every level and error exist, and `G ↷ (X, μ)` is sofic.
7. **Theorem C.** `φ(ω) = ω(Γ)` is `Γ`-invariant, since `γ'Γ = Γ` for `γ' ∈ Γ`. So `g·φ`, `ω ↦ ω(gΓ) = ω(c)`,
   lies in `L^∞(X, μ)^Γ`. Invariance under `γ` gives `ω(c) = (γ^{-1}ω)(c) = ω(γc) = ω(c')` `μ`-a.e.,
   contradicting step 5. ∎
8. **Subrings.** Steps 1–7 use only elements of a `G`-stable subring containing `x_c` and `δ^(-1)`. Such a
   subring contains `δ = x_c - σ_γ x_c` and every `x_d`, since `H` is transitive. ∎

**COMPLETE.**
