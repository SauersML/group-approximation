---
rg: 2
id: native-t00-collision-first-hecke-gl10-proof
kind: route
title: Resolve the collision against B2 as two transverse paths in the marked GL10 chart
target: native-t00-collision-first-hecke-attachment-has-gl10-model
requires:
  - native-t00-y1-collision-pays-marked-opnorm
  - marked-t00-separation-has-gl10-model
  - native-a1-b2-hecke-triangle-has-gl7-model
  - outer-root-leavitt-table
---

Prefix cancellation gives

```text
db_2
 =(t_00+s_0t_00)s_00t_1
 =t_1+s_0t_1
 =b_0+b_1.                                             (1)
```

Since the roots `(7,8)` and `(8,4)` are composable, the ordinary Steinberg
commutator law turns `(1)` into `(THF3)`.  The factors `H_0,H_1` commute
because they lie in the same abelian root subgroup.  Also

```text
b_0s_1=t_1s_1=1,                                      (2)
```

so `H_0` is a genuinely nonzero full-rank-scale root occurrence.

For the finite fence, use the ten vertices and all assignments from
`marked-t00-separation-has-gl10-model`.  Add the already established native
triangle assignments `(THF4)--(THF5)`.  Direct transvection multiplication
gives

```text
[D,B_2]=e_(7_0,6)e_(b,6)=H_1H_0.
```

The new edge `e_(b,6)` does not enter the three-dimensional subspace
`<6,7_0,8_0>` carrying the native order-seven head.  Hence the calculations
`[B_2,A_1]=X_1` and `(J_1B_2A_1)^7=1` are exactly the old ones.  The marked
saturation row for `D` from the GL10 model is also unchanged, so its marked
child survives.  The MSI-only audit checks all these equalities.

The relation `(THF3)` is occurrence-typed at `B_2`, but it is not
projection-typed: no relation in this packet names the signed-Hecke source
cut.  The exact model therefore fences the inference from a nonzero mixed
ejection to positive paid mass on that source.
