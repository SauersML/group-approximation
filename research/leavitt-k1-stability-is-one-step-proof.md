---
rg: 2
id: leavitt-k1-stability-is-one-step-proof
kind: route
title: The matrix shadows of the Steinberg identities D j = j j and j = D Σ, and the unitary u on the e-corner
target: leavitt-k1-stability-is-one-step
requires:
  - leavitt-stabilization-kernels-are-one-step
  - leavitt-surjective-k2-stability-implies-injective
  - leavitt-refinement-identifies-unstable-k2-levels
---

**Item 1.**
- `α_(n+1)` splits the last coordinate `n + 1` by `(e*, f*)`. On `A ⊕ 1`, that coordinate carries the identity, so
  `T (A ⊕ 1) U = A ⊕ I_2`.
- `α_(n+1)` maps `E_(n+1)` onto `E_(n+2)`, so it is injective on `GL/E` classes. Hence
  `ker(s_(n+1) s_n) = ker(α_(n+1) s_n) = ker s_n`.
- By induction, every iterated stabilization has kernel `ker s_n`. Since `K_1 = colim GL_m/E_m`, this is the kernel of
  `GL_n/E_n -> K_1(R)`.

**Item 2.**
- `α_n(τ_e(A)) = T_n (E A E* + 1 - EE*) U_n = A ⊕ 1`. On the first `n - 1` coordinates both sides are `A`. The last
  coordinate `x` goes through `e* x`, and `U_n`, `T_n` split and rejoin it by `(e, f)`. The `E`-part reproduces the last
  row and column of `A` on the `e`-half, and `1 - EE*` puts the identity on the `f`-half. This is the matrix image of
  `j_N = D_N Σ^(e)`.
- `τ_e` preserves `E_n`, since `τ_e(t_ij(a))` is elementary. So `s_n = α_n τ_e` on classes.
- **`τ_e = c_U` on the image.** `U E = E²`, because `u e = e e`. Then `U τ_e(A) U* = E² A E*² + 1 - E² E*² = τ_e(τ_e(A))`.

**Item 3.**
- `α_n` is a bijection on classes. So `s_n` onto means that every class is `[τ_e(A')]`.
- Let `τ_e(H) in E_n` and write `H = τ_e(A') X` with `X in E_n`. Then `τ_e(H) = τ_e(τ_e(A')) τ_e(X) = c_U(τ_e(A')) τ_e(X)`.
- `c_U` preserves `E_n`, because `U` is an invertible diagonal matrix and `U t_ij(a) U^-1 = t_ij(u_i a u_j^-1)`. Also
  `τ_e(X) in E_n`. So `τ_e(A') in E_n`, and then `H in E_n`.
