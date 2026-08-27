---
rg: 2
id: sl3-arithmetic-double-near-exact-vertices-fold-projectively
kind: claim
title: Near-exact vertices of the SL3 arithmetic double fold projectively with a dimension-free bound
distinct_from:
  sl3-arithmetic-double-finite-representations-fold: that proves literal equality of the two vertices when the double representation is exact; this permits amalgam and vertex error and concludes the trace-square statement needed by the regular-double mark.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that assumes only the lattice restriction is near an exact lattice representation and classifies a quasi-regular leak by congruence level; this assumes both full A-vertex assignments are near exact and gives immediate projective fold collapse without a tower analysis.
---

Let `C=SL_3(Z)<=A=SL_3(Z[1/2])`, `D=A*_C A`, and fix finite
presentations and generating sets.  Suppose `sigma_n` are approximate
assignments of `D` with defect `delta_n->0`.  Write `pi_(n,j)` for their two
vertex assignments.  If there are exact representations
`alpha_(n,j):A->U(d_n)` such that on the fixed vertex generators

```text
max_x ||pi_(n,j)(x)-alpha_(n,j)(x)||_2 <= epsilon_n -> 0
                                                             (ANV1)
```

for `j=0,1`, then for every fixed `a in A`, and in particular for
`h=diag(2,1,1/2)`,

```text
|tr(pi_(n,0)(a) pi_(n,1)(a)^*)| -> 1.                        (ANV2)
```

The convergence has a dimension-free modulus depending only on the fixed
word for `a`, the presentation, and the constant in
`exact-projective-codensity-has-a-uniform-trace-square-gap`.

Consequently any canonical-character microstate enemy for the arithmetic
double must keep at least one of its two full `A`-vertex restrictions a
uniform normalized-HS distance from every exact finite-dimensional
representation along a subsequence.  It cannot live in the joint near-exact
sector.

