---
rg: 2
id: window-lef-subshifts-give-matricial-crossed-products-proof
kind: route
title: Partial permutation models exact on windows define injective partial ring homomorphisms of the crossed product
target: window-lef-subshifts-give-matricial-crossed-products
requires:
  - rf-subshifts-are-periodic-window-approximable
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part1.md
---

Full derivation in the artifact, §2. Outline:

1. **Transport identity.** `c_(β(g)z)(gλ) = c_z(λ)` for `λ, gλ ∈ B_r`, by the partial-homomorphism rule applied to `λ^(-1)g^(-1)` and `g`. Also `β(g^(-1)) = β(g)^(-1)`.
2. **Local freeness is automatic.**
   - Freeness and compactness give, for `s ≠ e`, a finite `V_s` with `x|_(V_s) ≠ (s^(-1)·x)|_(V_s)` for all `x ∈ X`.
   - If `β(s)z = z` for such an `s`, the transport identity makes the pattern `c_z`, which is a pattern of `X`, agree with its `s^(-1)`-translate on `V_s`. That is a contradiction.
   - So `β` is injective on small balls, and `Γ` is LEF (item 1).
3. **Model map.** Put `D(f)δ_z = F(c_z|_(W_f))δ_z`, which is well defined since every `c_z` is a pattern of `X`, and `P_g δ_z = δ_(β(g)z)`.
   - Pointwise evaluation makes `D` additive and multiplicative.
   - The transport identity gives `P_g D(f) P_g^(-1) = D(f∘α(g^(-1)))`, and the partial-homomorphism rule gives `P_g P_h = P_(gh)`.
   - So every listed sum and product is preserved once `r` is large relative to the list.
4. **Injectivity.**
   - For `a = Σ f_g u_g ≠ 0`, pick `g_0` with `f_(g_0)(x) ≠ 0`, `z` with `c_z = x|_(B_r)`, and `z' = β(g_0^(-1))z`.
   - The `g_0`-term of `φ(a)δ_(z')` is nonzero at `δ_z`.
   - Every other term lands at `β(g g_0^(-1))z ≠ z` by local freeness.
5. **Ultraproduct.** Let `r_n -> ∞`. Relations and non-vanishing hold for all large `n`, which gives item 2.
6. **Item 3.** `GL_M(R) ↪ ∏_ω GL_(MN_n)(F_q)`, and a countable subgroup of an algebraic ultraproduct of finite groups is LEF.
7. **Item 4.**
   - For `Γ = ⟨S | ℛ⟩` with relators of length `<= r`, the partial-homomorphism rule makes `β|_S` satisfy every relator. So it extends to a genuine action `β'` agreeing with `β` on `B_r`.
   - The configurations `y_z(λ) = c(β'(λ^(-1))z)` form a finite invariant subset of the window SFT covering `L_(B_r)(X)`, which is window periodicity.
   - The converse is immediate, and `rf-subshifts-are-periodic-window-approximable` gives the equivalence with residual finiteness. ∎
