---
rg: 2
id: finite-spectrum-unitary-power-recurrence
kind: claim
title: Every d-dimensional unitary has a Q^-1 return by time Q^d
distinct_from:
  summable-power-return-detectors-miss-growing-cycles: that is a no-go for a fixed weighted sum of moments; this is an adaptive existence theorem selecting one power after the finite coordinate is fixed.
  finite-cocycle-select-has-an-exact-power-return: that is a special exact second-power identity in one finite packet; this is uniform finite-spectrum recurrence for every unitary matrix.
---

For every `W in U(d)` and integer `Q>=2`, some `1<=m<=Q^d` satisfies

```text
||W^m-I||_op <= 2*pi/Q.
```

Diagonalize `W`, place the `Q^d+1` points `0 theta,...,Q^d theta` in the
`Q^d` cubes of the `d`-torus, and subtract two points in the same cube.  This
is an elementary finite-dimensional lemma with no literature input.  Lean now
checks the qualitative form sufficient downstream—every finite-dimensional
unitary has a positive power arbitrarily close to `1`—as
`CollisionCapacityDetectors.exists_positive_power_opNorm_sub_one_lt`.
The sharper numerical bound `m <= Q^d` remains paper-level; downstream UPR
remains open regardless.
