---
rg: 2
id: extraspecial-packet-holonomy-folding-proof
kind: route
title: Send stable edges to their packet automorphisms
target: isomorphic-extraspecial-packet-complex-folds
requires: []
---

Choose a maximal tree in the underlying graph.  Use its edge identifications
to identify every vertex packet with one reference copy `K`.  A non-tree
edge then contributes one automorphism `alpha_e in Aut(K)`.  Map every
vertex group into the normal copy of `K` in `K semidirect Aut(K)` and map the
stable letter of `e` to `alpha_e`.  The Bass--Serre conjugacy relation is
exactly

```text
alpha_e k alpha_e^-1 = alpha_e(k),
```

so this defines the quotient `(IEP1)`.

The center of an extraspecial group is characteristic.  Hence every
`alpha_e` fixes its unique nontrivial central element `J`, and all vertex
marks map to the same nontrivial element.  Any faithful unitary
representation of the finite quotient supplies the asserted fixed
dimensional marked model.

