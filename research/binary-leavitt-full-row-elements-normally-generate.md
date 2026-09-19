---
rg: 2
id: binary-leavitt-full-row-elements-normally-generate
kind: claim
title: Every nonidentity element of a full binary-Leavitt root row or column normally generates the Steinberg group
artifacts:
  - GroupApproximation/Steinberg/BinaryLeavitt.lean
distinct_from:
  full-leavitt-idempotent-defect-saturation: that proves normal generation for the single distinguished idempotent root x_13(q); this isolates a nonzero coefficient root from an arbitrary element of a full commuting row or column module.
  binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale: that gives quantitative rank comparison and overlap bounds for rounded root cuts in matrix coronas; this is a purely algebraic normal-closure statement and uses no corona representation.
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that is the open analytic exclusion of the Haar profile; this supplies only the algebraic normal-generation input used after character diracization.
---

Let `R=L_(F_2)(1,2)`, `Delta=St_n(R)`, and `n>=5`.  Fix a row index `i`
and write an element of its full root row as

```text
v=product_(j!=i) x_ij(a_j).
```

If `v!=1`, then

```text
normalClosure_Delta({v})=Delta.                          (FRN1)
```

The same conclusion holds for every nonidentity element of a full root
column

```text
v=product_(i!=j) x_ij(a_i)
```

with the target index `j` fixed.

This is qualitative normal generation, not a uniform word-length or corona
rank estimate.  It is exactly the amount of algebra needed to show that the
scalar kernel of a nontrivial character meets a full root row or column only
at the identity.

