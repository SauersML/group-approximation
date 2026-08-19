---
rg: 2
id: atlas-h-bridge-paired-system-is-scaling-inert-proof
kind: route
title: H and the bridge root generate the diagonal A8 subgroup
target: atlas-h-bridge-paired-system-is-scaling-inert
requires:
  - paired-finite-group-intertwiner-laplacian
  - regular-paired-finite-group-relations-are-balanced
artifacts:
  - docs/TRUE_ATLAS_SINGLE_BRIDGE_SUBGROUP_REDUCTION.md
---

The bridge artifact proves `<H,b>=A_8`.  Hence the relation pairs in `(AHB1)`
generate

```text
K={(g,g):g in A_8} <= A_8 x A_8.
```

Both coordinate projections of this diagonal subgroup are isomorphisms.  By
`regular-paired-finite-group-relations-are-balanced`, the two pulled-back
regular representations are identical up to unitary equivalence and their
intertwiner space contains a unitary.

More concretely, `paired-finite-group-intertwiner-laplacian` identifies the
zero-energy space with

```text
Hom_(A_8)(Reg_A8,Reg_A8),
```

which is the right regular group algebra.  It contains every right translation,
so no subspace can be shrunk by it.  Every spectral low-energy space contains
this zero-energy space and is equally incapable of shrinkage.
