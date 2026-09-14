---
rg: 2
id: amenable-crossed-products-meet-stepanov-condition-b-proof
kind: route
title: Dimension count over one cylinder and one Følner set
target: amenable-crossed-products-meet-stepanov-condition-b
requires: []
artifacts:
  - research/artifacts/sk-stable-rank-b-stepanov-route-2026-09-13.md
---

**Conventions.** `u_γ f u_γ^{-1} = f∘γ^{-1}`, so `f u_γ = u_γ (f∘γ)` and `u_γ e_U = e_(γU) u_γ`. The `u_γ` form a
basis of `R` as a left `LC(X,K)`-module.

**Item 1.** Write `p = Σ_(k∈S) f_k u_k` and `q = Σ_(k∈S) g_k u_k` with `S ⊆ Γ` finite.

1. **Følner set.** Choose a finite nonempty `F ⊆ Γ` with `|kF ∖ F| < |F|/|S|` for every `k ∈ S`. It exists because
   `Γ` is amenable. Then `SF ⊆ F ∪ ⋃_(k∈S)(kF ∖ F)`, so `|SF| < 2|F|`.
2. **Cylinder.** The functions `f_k∘m` and `g_k∘m`, for `k ∈ S` and `m ∈ SF`, are finitely many and locally constant.
   So some nonempty clopen `U ⊆ X` has all of them constant on `U`. Write `c_(k,m)` and `d_(k,m)` for their values there.
3. **Linear map.** For `ρ ∈ K^F` put `r_ρ = Σ_(g∈F) ρ_g u_g e_U`. Since `f_k u_(kg) e_U = u_(kg)(f_k∘kg) e_U
   = c_(k,kg) u_(kg) e_U`,

   ```text
   p r_ρ = Σ_(k∈S, g∈F) ρ_g f_k u_(kg) e_U = Σ_(m∈SF) (Pρ)_m u_m e_U,   (Pρ)_m = Σ_(kg=m) c_(k,m) ρ_g .
   ```

   Likewise `q r_σ = Σ_(m∈SF) (Qσ)_m u_m e_U` with `d` in place of `c`.
4. **Count.** `(ρ, σ) ↦ Pρ + Qσ` is a linear map `K^F × K^F → K^(SF)` and `2|F| > |SF|`. So it has a nonzero kernel
   vector `(ρ, σ)`. Put `r = r_ρ` and `s = r_σ`, so `pr + qs = 0`.
5. **Nonzero.** The coefficient of `u_g` in `r_ρ` is `ρ_g e_(gU)`. It is nonzero whenever `ρ_g ≠ 0`, because `U ≠ ∅`.
   So `r ≠ 0` or `s ≠ 0`.

For `Γ = Z` take `S = [−w, w]` and `F = [0, 2w]`. Then `|SF| = 4w+1 < 4w+2 = 2|F|`, and `U` only needs the coefficients
composed with `T^m`, `|m| ≤ 3w`, to be constant.

**Item 2.** For `a ∈ GL_n(R)` with `n ≥ 3`, item 1 gives `(r, s) ≠ 0` with `a_12 r + a_13 s = 0`. The column
`α = (0, r, s, 0, …, 0)^T` is nonzero, `α_1 = 0`, and `(aα)_1 = a_11·0 + a_12 r + a_13 s = 0`. The scalars multiply
columns on the right, matching Stepanov's `t_(*i)(αλ)` on p. 2152.
