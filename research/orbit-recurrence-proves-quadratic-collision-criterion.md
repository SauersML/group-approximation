---
rg: 2
id: orbit-recurrence-proves-quadratic-collision-criterion
kind: route
title: Solve the quadratic difference equation along runs on each shared-shift orbit
target: quadratic-shift-differences-have-exact-orbit-criterion
requires: []
artifacts:
  - research/artifacts/gottschalk-exact-quadratic-derivative-collision-criterion-2026-09-08.md
---

On an orbit write the difference equation as

    q_i=delta_i x_(i+1)+delta_(i+1)x_i+delta_i delta_(i+1).

Edges with both delta values zero give the first condition. At a
zero between two ones, both incident edge equations prescribe the
same x value, giving the second condition. These conditions allow
all zero vertices to be assigned consistently.

On a run of ones the remaining equations are
x_i+x_(i+1)=q_i+1. Solve successively on every path. A full finite
all-one orbit closes consistently exactly under the parity condition.
The proof includes loops and double edges for t of order one and two,
as well as recurrence in both directions on infinite orbits.

For F=x+A Q_t, a collision has delta=Aq. Conversely the criterion
constructs x for any admissible q, and linearity gives
F(x+delta)+F(x)=delta+Aq=0. Nonzero delta makes the inputs distinct.
