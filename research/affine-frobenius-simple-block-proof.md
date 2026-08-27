---
rg: 2
id: affine-frobenius-simple-block-proof
kind: route
title: Induce one nontrivial translation character and exhaust the Plancherel sum
target: affine-frobenius-group-has-almost-full-simple-block
requires: []
---

Normality of `N` makes `e_N` central, and its identity coefficient is `1/p`,
giving `(AFB2)`.  The quotient `H_p/N=F_p^x` supplies `p-1` one-dimensional
representations.  The complement acts freely and transitively on the `p-1`
nontrivial characters of `N`; inducing any one of them gives a single
irreducible representation of dimension `p-1`.  The dimension count

```text
(p-1)*1^2+(p-1)^2=p(p-1)=|H_p|                       (AFB4)
```

exhausts all irreducibles.  `e_N` is identity on the quotient characters and
zero on the induced representation, so `q_p` selects exactly its full matrix
block.

