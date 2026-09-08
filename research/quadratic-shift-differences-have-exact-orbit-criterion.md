---
rg: 2
id: quadratic-shift-differences-have-exact-orbit-criterion
kind: claim
title: Boolean shared-shift quadratic differences have an exact local and cycle-parity criterion
artifacts:
  - research/artifacts/gottschalk-exact-quadratic-derivative-collision-criterion-2026-09-08.md
---

For every group G, t in G, and delta,q in F_2^G, put Q_t(x)=x R_t x.
The equation Q_t(x+delta)+Q_t(x)=q is solvable if and only if:

1. q(g)=0 whenever delta(g)=delta(gt)=0.
2. q(gt^-1)=q(g) whenever delta(g)=0 and both its t-neighbors have
   delta value one.
3. On every finite t-orbit O on which delta is all ones,
   the sum of q on O is |O| modulo two.

For any linear CA A, the map F(x)=x+A Q_t(x) is noninjective exactly
when such a q exists with delta=Aq nonzero. Equivalently, the finite
local constraints on q have a global solution with (Aq)(1)=1.
The theorem does not assert existence of that solution.
