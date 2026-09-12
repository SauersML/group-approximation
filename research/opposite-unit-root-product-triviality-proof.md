---
rg: 2
id: opposite-unit-root-product-triviality-proof
kind: route
title: Braid relation in characteristic two collapses a vanishing opposite product to equal root operators, and a same-row commutator kills a root element
target: opposite-unit-root-product-vanishes-only-for-trivial-models
requires:
  - el4-model-trivial-on-one-unit-root-element-is-trivial
artifacts:
  - research/artifacts/rank-four-corner-endpoint-and-framing-2026-09-12.md
---

This is Section 5, Proposition 5 of the artifact. Relabel indices so that `(I, J) = (1, 3)`. Put
`X = n_13(1)` and `Y = n_31(1)`.

1. **Squares.** `x_13(1)^2 = x_13(2) = x_13(0) = 1`, so `(1 + X)^2 = 1`. Since `2 = 0` in `M`, this gives
   `X^2 = 0`, and likewise `Y^2 = 0`.
2. **Braid relation.** Over `Z`, the `(1,3)` blocks of `x_13(1) x_31(-1) x_13(1)` and
   `x_31(-1) x_13(1) x_31(-1)` both equal `[[0,1],[-1,0]]`. With `-1 = 1` in `R`, the matrix identity
   `x_13(1) x_31(1) x_13(1) = x_31(1) x_13(1) x_31(1)` holds in `GL_4(R)`, hence in `EL_4(R)`.
3. **Expansion.** Apply `sigma` and expand, using `2 = 0` and step 1:
   - `(1+X)(1+Y)(1+X) = 1 + Y + XY + YX + XYX`;
   - `(1+Y)(1+X)(1+Y) = 1 + X + XY + YX + YXY`.

   So `Y + XYX = X + YXY`.
4. **Collapse.** If `YX = 0`, then `XYX = YXY = 0`, so `X = Y`. Call `u = sigma(x_13(1)) = sigma(x_31(1))`.
5. **A root element dies.**
   - `x_13(1)` commutes with `x_12(r)`, since they share row 1. So `u` commutes with `sigma(x_12(r))`.
   - The Steinberg relation gives `x_32(r) = [x_31(1), x_12(r)]`.
   - Hence `sigma(x_32(r)) = [u, sigma(x_12(r))] = 1`.
6. **Conclusion.** `sigma(x_32(1)) = 1`, so `sigma` is trivial by
   `el4-model-trivial-on-one-unit-root-element-is-trivial`.
7. **Positivity.** In a rank ultraproduct, `e YX = YX` gives `rk(e) >= rk(YX)`. That rank is positive by
   faithfulness whenever `sigma` is nontrivial.

**Calibration.** In the honest model `EL_4(F_2) <= GL_4(F_2)`, `YX = E_31 E_13 = E_33 != 0`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 9.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
