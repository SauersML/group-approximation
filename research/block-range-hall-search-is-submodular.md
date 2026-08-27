---
rg: 2
id: block-range-hall-search-is-submodular
kind: claim
title: The best block-range Hall certificate is a submodular minimization problem
---

In the setting of `block-range-hall-implies-shrunk-subspace`, define on source
block subsets `A` the deficit objective

```text
f(A) = sum_j dim(R_j(A)) - sum_(i in A) dim(H_i).       (BRH3)
```

Then `f` is a submodular set function.  Consequently the strongest certificate
of the coordinate-block form `(BRH1)` is obtained by minimizing `f`; a negative
minimum `f(A)=-r` certifies an `r`-shrunk subspace.

This turns the finite-coordinate search into a standard theoretical-computer-
science primitive rather than a generic noncommutative-rank black box.  For a
small fixed Fourier alphabet one can simply enumerate source-block subsets; at
larger alphabets one may use any exact submodular-function minimization method
with the range-dimension computation as a value oracle.
