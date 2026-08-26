---
rg: 2
id: clifford-direct-sum-dilution-proof
kind: route
title: Quantize each Pauli curvature and apply the weighted union bound
target: clifford-direct-sum-dilution-forces-an-exact-good-block
requires: []
---

For a nonidentity Pauli `P_a` in an irreducible Clifford block,
`tr(P_a)=0`.  Therefore, for unit scalars `lambda,mu`,

```text
||lambda P_a - mu 1||_2^2 = 2.
```

For `a=0` the curvature is itself a unit scalar, so its distance to the
unit-scalar set is zero.  Orthogonality of a finite direct sum gives `(DSD1)`
after weighting block `i` by `dim(H_i)/dim(H)`.

If each of the `m` tested curvatures has squared distance from `1` below
`2/m`, `(DSD1)` says that its bad blocks have total weight below `1/m`.
The weighted union bound makes the union of all bad-block sets have weight
strictly below one.  A block outside that union has zero phase-space label on
every tested multiplication triangle.  Tensoring a Pauli by an identity
does not change its normalized trace, so the same proof covers arbitrary
tensor padding of the constituents.

