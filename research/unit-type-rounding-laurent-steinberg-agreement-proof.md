---
rg: 2
id: unit-type-rounding-laurent-steinberg-agreement-proof
kind: route
title: The inverse-root defects commute with the Kazhdan mixed-level root group, whose finite images equal those of the vertex
target: unit-type-vertex-rounding-agrees-with-sigma-on-laurent-steinberg
requires:
  - laurent-extension-agrees-iff-inverse-defects-commute
  - mixed-level-root-group-is-kazhdan-in-rank-at-least-five
artifacts:
  - research/artifacts/hs-extension-laurent-descent-2026-09-13.md
---

Full derivation in §1 of the artifact. Put `h = x_i^(-1)`, `U = σ(e_23(h))`, `V = ρ'(x_23(h))`, so `W_i = V^*U`.
Put `π(e_cd(f)) = σ(e_cd(f)) = ρ'(x_cd(f))` for `f ∈ R_+`.

1. **Full roots.** If `c ≠ 3` and `d ≠ 2`, or `(c,d) = (2,3)`, both `U` and `V` commute with `π(e_cd(f))`, hence so does `W_i`.
2. **Row 3.** For `k ∉ {2,3}`, `[x_23(h), x_3k(x_i a)] = x_2k(a)`. With `b = π(e_3k(x_i a))`, both
   `UbU^*b^*` and `VbV^*b^*` equal `π(e_2k(a))`. So `UbU^* = VbV^*` and `W_i b = b W_i`.
3. **Column 2.** For `k ∉ {2,3}`, `[x_k2(x_i a), x_23(h)] = x_k3(a)` gives the same for `b = π(e_k2(x_i a))`.
4. **Corner.** `e_32(x_i^2 a) = [e_3k(x_i a), e_k2(x_i)]`, with a third index `k`, since `r >= 5`.
5. So `W_i` commutes in `M` with all generators of `K_i = K(R_+, x_i)`.
6. **Same image.** `x_i ∈ A_n^×` and `R_+ -> A_n` onto give `π_n(e_cd(x_i^e R_+)) = π_n(e_cd(R_+))`, so
   `π_n(K_i) = π_n(Γ)`.
7. **Kazhdan projection.** Take a Kazhdan pair `(S_K, κ_K)` of `K_i` (second premise) and representatives `(w_n)`
   of `W_i`. Then `||w_n - E_n w_n||_2 <= κ_K^(-1) max_(s ∈ S_K) ||[w_n, π_n(s)]||_2 -> 0`, with
   `E_n w_n ∈ π_n(Γ)'`. So `W_i ∈ prod_U π_n(Γ)' ⊆ π(Γ)' ∩ M`.
8. **Conclusion.** Item 2 of the first premise: `σ∘q = ρ'` on `St_r(L)`.
