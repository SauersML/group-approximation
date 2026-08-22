---
rg: 2
id: sl3-gao-carrier-has-uniform-popa-compactness
kind: claim
title: Every scalar Gao witness for the SL3 inclusion admits one uniform scalar-compact carrier deformation
distinct_from:
  gao-hyperfinite-carriers-do-not-give-popa-compactness: that proves this does not follow formally from coordinate hyperfiniteness; this is the additional arithmetic uniformity statement that would be sufficient.
  sl3-canonical-double-has-a-correctable-vertex: that asks to correct a matrix representation vertex; this asks only for a compact completely positive deformation on the Gao carrier containing the lattice factor.
---

OPEN.  Suppose a scalar-coefficient Gao witness embeds

```text
P=L(SL_3(Z)) subset M=L(SL_3(Z[1/2]))
```

into `calA=prod_omega A_k` with commuting-square carrier
`calB=prod_omega B_k`, each `B_k` hyperfinite.  There are normal subunital,
subtracial completely positive maps

```text
Phi_j:calB -> calB
```

which converge pointwise in `L^2` to the identity on `P` and whose `L^2`
implementations are compact.

By `gao-hyperfinite-carriers-do-not-give-popa-compactness`, this is not a
formal consequence of hyperfiniteness of the coordinates.  It must use the
arithmetic inclusion and its simultaneous Hecke fusion data to prevent the
finite-dimensional approximation ranks from escaping with `k`.
