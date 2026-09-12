---
rg: 2
id: matrix-unit-root-rank-models-propagation-proof
kind: route
title: Commutation with the unit matrix units and two commutator expansions force block support of every root element
target: matrix-unit-root-rank-models-of-simple-el3-are-trivial
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

Complete proof: artifact Section 4c, Proposition 6 and Corollary 7.

Write `M` as `4 x 4` blocks over `(p_1, p_2, p_3, f)` with `u_ij = E_ij`. In characteristic
two every `n_ij(a) = sigma(x_ij(a)) - 1` squares to zero, and a commutator of root elements
expands as `xy + yx + xyx + yxy + xyxy`.

- Commutation of `x_13(a)` with `x_12(1)` and `x_23(1)` puts `n_13(a)` in the form
  `D(E_11+E_22+E_33) + C E_13 + P E_14 + Q E_43 + S E_44`.
- Expanding `x_12(a) = [x_13(a), x_32(1)]` and then `x_13(a) = [x_12(a), x_23(1)]` forces
  `D = P = S = 0`.
- Expanding `x_13(a) = [x_12(1), x_23(a)]`, after commutation of `x_23(a)` with `x_13(1)` and
  `x_21(1)`, forces `Q = 0`.
- So `n_13(a) = C(a) E_13`, and the remaining commutator identities give
  `n_ij(a) = C(a) E_ij` for every root.
- Additivity and `x_13(ab) = [x_12(a), x_23(b)]` make `C` a unital ring homomorphism into
  `p_1 M p_1`.
- That corner is directly finite. `ts = 1 != st` and simplicity of `R` give `p_1 = 0`, and
  the displacement bound of artifact Corollary 4 then kills every root element.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 22 (one ordering slip in artifact step 5: (1+D')C', not C'(1+D'); not load-bearing. Scope sharpening: block support of the six unit root elements on orthogonal idempotents already implies the matrix-unit hypotheses) of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
