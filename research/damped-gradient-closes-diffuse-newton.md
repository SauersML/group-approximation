---
rg: 2
id: damped-gradient-closes-diffuse-newton
kind: route
title: Iterate intrinsic adjoint-gradient descent on the compressed contraction tuple
target: balanced-overlay-diffuse-square-function-newton
requires:
  - aggregate-cut-compression-stores-boundary-as-involution-defect
  - damped-adjoint-step-bypasses-code-riesz-at-exact-base
  - off-base-row-gradient-coercivity
  - dense-complete-pair-remainders-are-cb-quadratic
---

Block compression produces an exactly reducing selfadjoint contraction
tuple, a diffuse row-column bound, and a vanishing positive involution
forcing floor.  Apply `(ORG1)` repeatedly.  Below a fixed basin threshold,
the `E^(3/2)` term is absorbed into the strict linear decrease, so the
energy converges geometrically to the forcing floor.  The sum of correction
distances is finite by Cauchy--Schwarz along the geometric sequence.

Finally apply coordinatewise spectral sign.  Its average squared movement
is at most the remaining involution residual, and bounded-width plus dense
averaging telescoping keeps every balanced relator vanishing.  The common
cut remains reducing throughout functional calculus.  This proves the
diffuse correction theorem without assembling the code-Riesz pseudoinverse.

