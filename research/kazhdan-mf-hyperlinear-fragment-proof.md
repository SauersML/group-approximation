---
rg: 2
id: kazhdan-mf-hyperlinear-fragment-proof
kind: route
title: Extract the Kazhdan corner and use simplicity to make the quotient faithful
target: kazhdan-mf-hyperlinear-fragment
requires: []
artifacts:
  - GroupApproximation/Sofic/KazhdanCorner.lean
---

## Direct proof

`Sofic/KazhdanCorner.lean` proves the first clause as the closed theorem

```text
hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF.
```

Property (T) supplies the Kazhdan spectral projection in the matrix
ultraproduct.  For a nontrivial weak-MF source the corresponding corner is
nonzero; compression gives a homomorphism into a tracial matrix ultraproduct
with nontrivial range, hence a nontrivial hyperlinear quotient.

For a simple source, the kernel of a nontrivial quotient is a proper normal
subgroup and therefore trivial.  Thus the quotient map is faithful and the
source itself is hyperlinear.  The composite is kernel-checked directly as

```text
isHyperlinear_of_simple_kazhdan_weakMF.
```
