---
rg: 2
id: fano-maximal-cap-overlap-proof
kind: route
title: Count cap incidences and telescope the projection sums inside the trace
target: fano-maximal-cap-overlap-has-positive-sequential-mass
requires:
  - rstar-fano-caps-have-seven-maximal-parity-covers
  - tracial-cap-menus-are-central-core-partitions
---

For fixed nonzero `t`, exactly half of all eight functionals take value one
on `t`, and the zero functional is not among them.  Thus exactly four
nonzero functionals contain `t`, proving `(FMO2)` after summing the atomic
PVM projections.

Expand the left side of `(FMO3)` as

```text
sum_lambda tau(E_m...E_1 E_1...E_m).
```

Sum first over `lambda_1`, use `E_1^2=E_1`, cyclicity of the trace, and
`sum E_1=4I`; this contributes a factor four and removes the first context.
Iterate through all contexts to obtain `4^m`.  There are `7^m` profiles, so
one term is at least `(4/7)^m`.
