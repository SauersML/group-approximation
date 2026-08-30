---
rg: 2
id: flat-calibrations-refute-bounded-degree-two-primitives
kind: claim
title: Packed flat calibrations force unbounded operator-norm degree-two primitives
distinct_from:
  bounded-degree-two-primitives-for-higher-rank-lattices: that asserts a uniform operator-norm right inverse on L2-exact 2-cocycles; this constructs packed regular-module coboundaries whose smallest bounded primitive norm diverges, hence proves its negation.
---

Let `N>=4`, let `Gamma=SL_N(Z)`, and fix a finite presentation complex `K`
for `Gamma`. There are constants `a,b,C_0>0`, depending only on `K` and
`N`, with the following property.

For every sufficiently large integer `R` there are a tracial matrix
ultraproduct `M_R`, an exact representation

```text
pi_R : Gamma -> U(M_R),
```

and a 2-cocycle `c_R` on `K` with coefficients in `M_R` under `Ad pi_R`
such that

```text
c_R = delta y_R for some M_R-valued 1-cochain y_R,
||c_R||_op <= C_0,
```

but every `M_R`-valued primitive `u` with `delta u=c_R` satisfies

```text
||u||_op >= a R / b.
```

In particular, there is no constant `C_N` giving operator-norm-controlled
primitives for all 2-cocycles that are coboundaries in `L^2(M_R)`. This
refutes [[bounded-degree-two-primitives-for-higher-rank-lattices]].
