---
rg: 2
id: odd-char-matrix-unit-root-rank-models-torus-proof
kind: route
title: Torus inversion of root elements and unipotence force block support in odd characteristic, and the corner ring homomorphism collapses
target: matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial
requires: []
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

Complete proof: artifact Section 4d, Proposition 8 and Corollary 9.

- On `SL_3(F_p)`, `sigma = Phi + f`, where `Phi` is the algebra homomorphism
  `M_3(F_p) -> M` defined by the matrix units.
- Commutation of `x_13(a)` with `x_12(1)` and `x_23(1)` gives
  `n_13(a) = D(E_11 + E_22 + E_33) + C E_13 + P E_14 + Q E_43 + S E_44`. This is triangular,
  so `n^p = 0` makes `D` and `S` nilpotent.
- `h = diag(-1,-1,1)` gives `sigma(h) sigma(x_13(a)) sigma(h)^-1 = sigma(x_13(a))^-1`. The
  entries give `2D + D^2 = 0`, `2S + S^2 = 0` and `2Q + QD + SQ = 0`, so `D = S = Q = 0`.
- `h' = diag(1,-1,-1)` gives `2P = 0`, so `P = 0`.
- Weyl elements transport `n_13(a) = C(a) E_13` to every root.
- Block-supported root actions are additive. `[1+X, 1+Y] = 1 + XY` gives
  `psi_13(ab) = psi_12(a) psi_23(b)`, and `C(a) = psi_12(a) u_21` is a unital ring
  homomorphism into `p_1 M p_1`.
- That corner is directly finite, and `R` is simple and not directly finite, so `p_1 = 0` and
  `sigma` is trivial.
