---
rg: 2
id: z3-constant-normal-rotation-proof
kind: route
title: Weights kill the mixed derivatives along the fixed line, and a rootless normal derivative is constant
target: z3-equivariant-automorphisms-have-constant-normal-rotation
requires: []
artifacts:
  - research/artifacts/z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md
---

Artifact Section 1.
1. By equivariance, `T` and `T^-1` map the fixed line into itself, so `T` acts there by `s -> s + b`.
2. Monomials of `T_u` have weight `a - b = 1 mod 3`. So along `Lambda` the only degree-one term is
   `lambda(s) u`, `T_u` vanishes, and `T_s` has no degree-one term in `(u, ubar)`.
3. The Jacobian at `(c, 0, 0)` is `diag(d_s T_s, lambda(c), lambdabar(c))`, with constant nonzero
   determinant. So `lambda` has no root in `F_2bar`, and is a constant.
4. The chain rule gives multiplicativity.
