---
rg: 2
id: dual-prefix-two-simultaneous-unit-orbits-proof
kind: route
title: Complete two selected cylinders to prefix codes and use their table unit
target: dual-prefix-heisenberg-table-has-two-simultaneous-unit-orbits
requires:
  - iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
  - leavitt-gl-equals-el-and-perfect-unit-group
---

If `alpha=beta`, complete `alpha` to a finite complete prefix code `P` and
complete `0` to a code `Q` of the same cardinality.  If `alpha!=beta`, do the
same with `alpha,beta in P` and `0,1 in Q`, matching `alpha` with `0` and
`beta` with `1`.  Binary leaf refinement increases cardinality by one, so
the two completions can always be chosen with equal size.

For the resulting bijection `p_i -> q_i`, put

```text
u=sum_i s_(q_i)t_(p_i),       u^(-1)=sum_i s_(p_i)t_(q_i).
```

The complete prefix relations give `u s_(p_i)=s_(q_i)` and
`t_(q_i)u=t_(p_i)`.  The selected entries are exactly `(DPU1)`.  Conjugation
by `diag(1,u,1)` then gives `(DPU3)`.  Finally use `GL=EL` in the fixed
stabilized rank to lift the conjugation to the Steinberg group.

