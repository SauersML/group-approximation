---
rg: 2
id: multilinear-collapse-defect-calibration-proof
kind: route
title: Compose two Toffoli gates and differentiate the multilinear representatives at (1,0,0)
target: multilinear-collapse-defect-does-not-obstruct-bijectivity
requires: []
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

Artifact, Section 6.1.
1. `T_1` and `T_2` are involutions, so `tau = T_2 T_1` and `sigma = T_1 T_2` are inverse
   bijections of `F_2^3`, hence of `(F_2^3)^G` sitewise.
2. Reduce `b^2 = b` to get the multilinear representatives. Substituting
   `y = (a + ab + bc, b, c + ab)` into `sigma = (y_1 + y_2 y_3, y_2, y_3 + y_1 y_2 + y_2 y_3)`
   gives coordinates `a + ab + ab^2` and `c + bc + b^2 c`.
3. The formal partial derivatives at `(1,0,0)` give `J_tau = [[1,1,0],[0,1,0],[0,1,1]]` and
   `J_sigma = [[1,0,0],[0,1,0],[0,1,1]]`. Their product is `I + e_12`.
4. The unreduced composites `(a + bc + ab^2, b, c + ab)` and `(a + bc, b, c + ab + b^2 c)` compose
   formally to the identity, so the pair is formalizable.
