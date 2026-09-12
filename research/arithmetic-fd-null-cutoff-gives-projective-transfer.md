---
rg: 2
id: arithmetic-fd-null-cutoff-gives-projective-transfer
kind: route
title: Apply the universal arithmetic cutoff to every selected projective leak
target: projective-trace-square-transfer-for-sl3-pair
requires:
  - arithmetic-leak-has-fd-null-laplacian-witness
  - arithmetic-selected-fd-null-cutoff-cannot-survive-matrices
  - projective-transfer-linear-bound-equals-no-ultraproduct-leak
---

If projective transfer failed, tensor amplification and ultraproduct
compactness would produce a selected projective leak of fixed size.  Formula
`(APW3)` makes `||gamma(y_N)T||_2` independent of `N` and bounded below,
whereas `(ASC1)` forces it to vanish.  This gives qualitative transfer; the
existing tensor-amplification equivalence upgrades it to the universal
linear trace-square modulus.
