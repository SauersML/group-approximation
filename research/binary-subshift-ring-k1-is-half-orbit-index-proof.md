---
rg: 2
id: binary-subshift-ring-k1-is-half-orbit-index-proof
kind: route
title: Bounded propagation makes half-orbit compressions Fredholm; elementary matrices compress to unipotents; the shift has index −1; K_1 = Z makes the surjection an isomorphism; flux equals average displacement
target: binary-subshift-ring-k1-is-half-orbit-index
requires:
  - minimal-cantor-crossed-product-k-theory-formula
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md
---

- **Representation.**
  - `π(u)π(f)π(u)^(−1)δ_n = f(T^(n−1)x)δ_n = π(f∘T^(−1))δ_n`, so `π` respects `u f u^(−1) = f∘T^(−1)`.
  - `π(Σ_j f_j u^j)` sends `δ_n` into `span{δ_(n+j) : |j| ≤ w}`.
- **Fredholm.**
  - `Pπ(M)P · Pπ(M^(−1))P = P − Pπ(M)(1−P)π(M^(−1))P`, and the correction has rank at most `kw`, by bounded propagation. The same holds on the other side.
  - Over a field, an operator invertible modulo finite rank has finite-dimensional kernel and cokernel.
  - The algebraic index is additive under composition and unchanged by finite-rank perturbations.
  - `Pπ(MN)P − Pπ(M)P·Pπ(N)P` has finite rank, so `ind` is a homomorphism. It is compatible with `M ↦ diag(M,1)`.
- **Vanishing on E.** For `i ≠ j`, `(Pπ(rE_ij)P)^2 = (Pπ(r)P)^2 ⊗ E_ij E_ij = 0`. So `Pπ(e_ij(r))P = I + nilpotent` is invertible, with index 0.
- **The shift.** `Pπ(u)P` is the unilateral shift on `span{δ_n : n ≥ 0}`: injective with cokernel `F_2δ_0`, so `ind(u) = −1`.
- **Isomorphism.** `ind` factors through `K_1(R_X) = GL(R_X)/E(R_X)` and is onto. By `minimal-cantor-crossed-product-k-theory-formula` over `F_2`, `K_1(R_X) ≅ (K^0 ⊗ F_2^×) ⊕ Z = Z`. A surjection `Z → Z` is bijective.
- **Consequences (a), (b).** `K_1 = GL/E` stably. An element of `EL_m` has index 0.
- **GPS index.**
  - `π(a_γ)δ_n = δ_(σ(n))` with `σ(n) = n + n_γ(T^n x)`, a bijection of `Z` with displacement at most `w`.
  - The compression kills `δ_n` for `n ≥ 0, σ(n) < 0`, and misses `δ_m` for `m ≥ 0, σ^(−1)(m) < 0`. So `ind(a_γ) = #{n ≥ 0 : σ(n) < 0} − #{n < 0 : σ(n) ≥ 0} = −φ`, where `φ` is the flux across `0`.
  - The flux across every cut is the same integer, so `Σ_(n=a)^(b) (σ(n) − n) = φ·(b−a) + O(w²)`.
  - For an invariant probability `μ` (Krylov–Bogolyubov) and `μ`-almost every `x`, Birkhoff gives averages converging to `∫ n_γ dμ = I(γ)`. So `φ = I(γ)`.
  - The index does not depend on `x`, since it is a homomorphism `K_1 → Z` with `ind(u) = −1`. ∎
- **Model test.** `γ = T` has `a_γ = u` and `I(T) = 1`, so `ind = −1` ✓. A finite-order `γ` has a unit of finite order, so its index is 0 ✓.
