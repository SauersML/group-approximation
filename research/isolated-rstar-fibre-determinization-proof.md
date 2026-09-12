---
rg: 2
id: isolated-rstar-fibre-determinization-proof
kind: route
title: Select one positive atom in each binary fibre and solve two character equations
target: isolated-rstar-context-determinizes-to-a-fano-cap
requires:
  - rstar-cap-support-is-one-character-row
---

The two spectral projections in `(IRC2)` are orthogonal and sum to the
identity.  On each active projection, `(IRC3)` assigns the three signs of a
chosen allowed atom, so the new observables are commuting self-adjoint
involutions and `(IRC4)` holds fibrewise.

There are at most two selected nonzero tail vectors.  One equation
`lambda dot u=1` has a nonzero solution.  For two active fibres the vectors
are distinct and hence independent over `F_2`; the two equations with
right-hand side one are therefore consistent.  Equation `(IRC6)` follows by
evaluating on `P_0,P_1`, and
`rstar-cap-support-is-one-character-row` identifies its support with the cap
in `(IRC7)`.
