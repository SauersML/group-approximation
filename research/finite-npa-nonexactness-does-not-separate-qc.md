---
rg: 2
id: finite-npa-nonexactness-does-not-separate-qc
kind: claim
title: Finite-level NPA non-exactness carries no separation between the quantum and commuting-operator sets
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

Neither the minimal-scenario non-exactness theorem nor the critical-tilt
overshoot theorem implies

```text
closure(Q)  !=  Q_c
```

in the `(2,2,2)` scenario, and no route in this graph may consume them as if
they did.

The reason is that the standard levels decrease to the commuting-operator set,
`intersection over k of Q_k = Q_c`.  A decreasing family can have every member
strictly larger than its limit; "no `Q_k` equals `closure(Q)`" is therefore
compatible with `closure(Q) = Q_c`, and is even what one expects when the two
coincide, since the intersection is attained only in the limit.  What the
theorems locate is the *rate* and the *mechanism* of approach -- a cubic contact
order at the critical tilt, a Motzkin sum-of-squares obstruction in the minimal
scenario -- not a gap between the two sets.

The practical consequence for this repository: results of this family are
evidence about the geometry of the NPA tangent cone and about the cost of
certification, and are not inputs to the Connes-embedding, hyperlinearity, or
soficity lanes.  A separation usable there has to come from a source that
exhibits a behaviour or trace in `Q_c` and outside `closure(Q)`, which these do
not.
