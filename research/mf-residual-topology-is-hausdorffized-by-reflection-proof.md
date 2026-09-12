---
rg: 2
id: mf-residual-topology-is-hausdorffized-by-reflection-proof
kind: route
title: Identify the identity closure with the intersection of MF kernels
target: mf-residual-topology-is-hausdorffized-by-reflection
requires:
  - countable-mf-groups-are-epireflective
  - mf-relation-closure
  - mf-radical-product-and-restricted-sum-formulas
---

The kernels in the definition are normal subgroups, are closed under finite
intersection by taking product target maps, and are invariant under left and
right translation.  They therefore define a group topology.

An element lies in every identity neighborhood exactly when every map to an
MF group kills it.  The universal quotient theorem identifies that
intersection with `Rad_MF(G)`, proving `(MT1)`.  Quotienting a topological
group by the closure of its identity is its universal Hausdorff quotient.
The MF adjunction shows that this quotient has exactly the same universal
property as `R_MF(G)`.

Apply `(MT1)` intrinsically to `G/N`.  The relation-closure formula

```text
mfroot_G(N)=q^(-1)(Rad_MF(G/N))
```

is precisely `(MT2)`.  The Hausdorff criterion follows from faithfulness of
the radical quotient.
