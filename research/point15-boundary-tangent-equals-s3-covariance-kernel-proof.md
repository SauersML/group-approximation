---
rg: 2
id: point15-boundary-tangent-equals-s3-covariance-kernel-proof
kind: route
title: Compute the rational boundary nullspace and test the H Gram matrix
target: point15-boundary-tangent-equals-s3-covariance-kernel
requires: []
artifacts:
  - experiments/atlas_boundary_h_exact_point15.py
  - experiments/atlas-boundary-h-exact-point15.json
---

The committed exact-integer construction gives `225 x 225` Gram matrices
`G_B` and `G_H`.  SymPy rational elimination computes

```text
rank_Q(G_B)=212,
dim_Q ker(G_B)=13,
rank_Q(G_H)=212.
```

It then computes an exact rational basis of `ker(G_B)` and verifies, with
exact arithmetic, that `G_H v=0` for every basis vector `v`.  Hence

```text
ker(G_B) subset ker(G_H).
```

Both kernels have dimension thirteen, so they are equal.  Since for a Gram
matrix `J^*J` over the reals the kernel is exactly the kernel of `J`, this is
`ker(J_B)=ker(J_H)`.

The script exits nonzero unless the exact equality holds; the committed JSON
records the successful certificate.  No floating-point or modular-rank step is
used in this proof.
