---
rg: 2
id: sofic-radical-linear-action-proof
kind: route
title: Amplify qualitative sofic-radical control to a linear modulus
target: sofic-radical-linear-action-criterion
requires: []
artifacts:
  - notes/TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md
---

## Direct proof

First, the image of `w` is in `Rad_sof(P)` exactly when every sequence of
finite `F`-actions with total relator defect tending to zero also has
`d_rho(w)` tending to zero.  A sequence violating this implication gives a
homomorphism from `P` to a metric ultraproduct of finite symmetric groups
which detects `w`.  Conversely, a sofic homomorphic image detecting `w`
pulls faithful sofic approximations back to such a violating sequence.

Suppose this qualitative criterion holds but no linear constant exists.
Choose actions with relator defect `a_n` and marked displacement `b_n`
satisfying `b_n > n a_n`.  Qualitative control forces `b_n -> 0`.  Take the
Cartesian power of the `n`-th action with
`m_n = ceil(1 / b_n)`.  Fixed-point fractions multiply, so the new total
relator defect is at most
`m_n a_n <= a_n / b_n + a_n -> 0`, whereas the marked displacement is at
least

\[
1-(1-b_n)^{1/b_n}\geq 1-e^{-1}.
\]

This contradicts qualitative control and proves a finite linear modulus.
The reverse implication is immediate.  Finally, decomposing a finite action
into transitive orbits expresses both sides as the same convex combination,
so the full and transitive-only formulations are equivalent.
