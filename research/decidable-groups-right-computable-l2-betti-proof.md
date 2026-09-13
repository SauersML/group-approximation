---
rg: 2
id: decidable-groups-right-computable-l2-betti-proof
kind: route
title: Heat-type moments decrease to the kernel dimension, and a log-determinant bound gives a computable rate
target: decidable-groups-have-right-computable-l2-betti-numbers
requires: []
---

**1.**
- Put `S = T^*T` and let `c >= 1` be an integer bounding the `ℓ¹` norm of its coefficients.
  Then `||S|| <= c`, and `μ`, the spectral measure of `S` under `Tr ⊗ τ`, lives on `[0, c]`
  with mass `k`.
- `a_n = (Tr ⊗ τ)((1 - S/c)^n) = ∫ (1 - λ/c)^n dμ(λ)` is rational. It is the identity
  coefficient of an explicit element, computable with the word problem.
- The integrands decrease pointwise to `1_(λ=0)`, so `a_n ↓ μ({0}) = dim_vN ker T`.

**2.**
- Choose `N` with `A = NT` integral, and put `c' = max(1, ||A^*A||_1)`. The determinant
  conjecture says `∫_((0,c']) log λ dμ_(A^*A) >= 0`.
- Split at `ε < 1`: the part `(0, ε]` contributes at most `μ_(A^*A)((0,ε]) log ε`, and the
  part `(ε, c']` at most `k log c'`. So `μ_(A^*A)((0, ε]) <= k log c' / log(1/ε)`.
- For `S` this reads `μ((0, ε]) <= k log c' / log(1/(N² ε))` when `N² ε < 1`.
- Then `a_n - dim_vN ker T <= μ((0, ε]) + k (1 - ε/c)^n`.
- Given `j`, choose `ε` making the first term `<= 2^(-j-1)`, then `n` with
  `k e^(-nε/c) <= 2^(-j-1)`. Both choices are computable. So `a_n` approximates
  `dim_vN ker T` within `2^(-j)`.
