---
rg: 2
id: centrally-finite-sterility-via-left-regular-action
kind: route
title: A centrally finite division ring is a finite-dimensional representation of its own unit group
target: compression-defect-dies-in-centrally-finite-division-rings
requires: [compression-defect-dies-in-finite-dimensions]
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

## Why sufficient

Let `D` be a division ring with `[D : Z(D)] < oo` and let
`rho : H -> D^x` be a homomorphism.  Put `F = Z(D)`; it is a field, and `D`
is an `F`-vector space of finite dimension by hypothesis.

Left multiplication `lambda_d(v) = dv` is additive, and `F`-linear because
`F` is central: `lambda_d(v f) = d v f = (lambda_d v) f` for `f in F`.  Each
`lambda_d` with `d != 0` is invertible with inverse `lambda_{d^{-1}}`, and
`lambda_{de} = lambda_d lambda_e`, so

    lambda : D^x -> GL_F(D)

is a group homomorphism.  It is injective: `lambda_d = id` gives `d = d.1 = 1`.

Now `lambda . rho : H -> GL_F(D)` is a finite-dimensional representation over
the field `F`, so by the prerequisite it kills `D(H,L)`.  Since `lambda` is
injective, `rho` kills `D(H,L)` too.

The whole step is the observation that the hypothesis "centrally finite"
literally hands you the finite-dimensional representation the prerequisite
needs; no property of the defect is re-examined.
