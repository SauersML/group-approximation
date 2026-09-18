---
rg: 2
id: harmonic-elimination-puts-q-in-odometer-crossed-products-proof
kind: route
title: At every point the translates by coset representatives take one wild value and a fixed multiset, and e_(d-1) minus S e_d cancels the wild value
target: harmonic-elimination-puts-q-in-odometer-crossed-products
requires: []
---

Lane proof (gq-deep-adelic-1), not independently reviewed. Notation as in the target.

1. **The functions lie in R.** For `γ ∈ T_M`, `f ∘ γ = u_γ^(-1) f u_γ ∈ R`. The `E_k` are integer
   polynomials in these commuting elements of `C(X, Q) ⊆ C(X, Q) ⋊_alg Γ`, so `E_k ∈ R`.
2. **Fix a point.** Let `x ∈ X` and `y = π(x) ∈ K`. Then `(f ∘ γ)(x) = f_K(γ y)`, and
   `(γ y)_M = γ · y_M` in `Γ/Γ_M`.
3. **The translates hit every class once.** `Γ_M` is normal, so `Γ/Γ_M` is a group and `y_M` is one of
   its elements.
   - `γ ↦ γΓ_M` is a bijection from `T_M` onto `Γ/Γ_M`, and right multiplication by `y_M` is a
     bijection of `Γ/Γ_M`.
   - So `γ ↦ (γ y)_M` is a bijection from `T_M` onto `Γ/Γ_M`.
   - Exactly one `γ_0 ∈ T_M` has `(γ_0 y)_M = (x_∞)_M`.
4. **Fixed values.** For `γ != γ_0`, the class `c = (γ y)_M` differs from `(x_∞)_M`. So
   `ℓ(γ y) = ℓ(c) < M`, which is determined by `c`, and `f_K(γ y) = 1/(1 + ℓ(c))`. By step 3 the
   multiset `{f_K(γ y) : γ ∈ T_M, γ != γ_0}` is
   `V_M = {1/(1 + ℓ(c)) : c ∈ Γ/Γ_M, c != (x_∞)_M}`, independent of `x`. Its elements are nonzero, with
   `Π V_M = 1/D_M` and `Σ_(v ∈ V_M) 1/v = S_M`.
5. **The wild value cancels.** Let `t = f_K(γ_0 y)`; it may be any value in `{1/(1+j) : j >= M} ∪ {0}`.
   - `E_d(x) = t Π V_M = t/D_M`.
   - `E_(d-1)(x) = Π V_M + t Σ_(v ∈ V_M) Π_(V_M ∖ {v}) = 1/D_M + t S_M/D_M`.
   - So `(E_(d-1) - S_M E_d)(x) = 1/D_M`.
   - `x` was arbitrary and `S_M ∈ Z`, so the constant `1/D_M` lies in `R`.
6. **Every level occurs.** Let `j < M`, and pick `g ∈ Γ_j ∖ Γ_(j+1)`, which exists because the chain is
   strict. The class `c = (x_∞)_M · gΓ_M` agrees with `(x_∞)_M` in `Γ/Γ_j`, since `g ∈ Γ_j`, and not in
   `Γ/Γ_(j+1)`. So `ℓ(c) = j` and `m_j >= 1`. Hence `Π_(j<M) (j+1)` divides `D_M`, i.e. `M! | D_M`.
7. **Conclusion.** For `m <= M`, `1/m = (D_M/m) · (1/D_M) ∈ R`. Taking `M` arbitrary gives `Q ⊆ R`.
