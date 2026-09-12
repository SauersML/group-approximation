---
rg: 2
id: fpbs-tree-projected-sphere-bubble-via-half-graph-transfer
kind: route
title: A contracting critical half-graph transfer matrix makes some critical fibre-sphere bubble small
target: fpbs-tree-projected-critical-sphere-bubble-below-one
requires:
  - fpbs-tree-projected-branch-share-last-crossing-bound
  - fpbs-tree-projected-critical-half-graph-transfer-below-one
---

Fix a tree-projected generating set `S`.
1. The second premise gives `chi^H_(p_c) < infinity` and `rho(N_(p_c)) < 1`.
2. By item 4 of the first premise, taken at `p_c`,
   `b_R(p_c) <= (chi^H_(p_c))^2 · 1^T N_(p_c)^(R-1) v_(p_c)`.
3. Fix `eps > 0` with `rho(N_(p_c)) + eps < 1`. The matrix is a fixed nonnegative
   `2n × 2n` matrix, so the right side is at most
   `C_eps (rho(N_(p_c)) + eps)^(R-1)`. This tends to 0, so `b_R(p_c) < 1` for
   some finite `R`, which is the target.

This is a genuine reduction, not a restatement. The premise concerns
one-step half-graph factors at criticality. The target concerns squared fibre
masses on a whole sphere of the quotient at some finite radius.
