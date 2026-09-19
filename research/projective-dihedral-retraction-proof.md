---
rg: 2
id: projective-dihedral-retraction-proof
kind: route
title: Round the second factor through the square defect
target: projective-dihedral-factorization-has-explicit-hs-retraction
requires: []
---

Since `A^2=epsilon I`, one has `A^(-2)=epsilon I`. Therefore

```text
D^2=A^(-1) C A^(-1) C
   =epsilon (A^(-1) C A) C,
```

which proves `(PDF3)` by right unitary invariance.

For `epsilon=1`, write `z=exp(i theta)` and
`c=|cos(theta)|`. The squared distance to `{1,-1}` is `2(1-c)`, while
`|z^2-1|^2=4(1-c)(1+c)`, proving `(PDF4)`. Multiplication by `i` gives the
case `epsilon=-1`. Borel functional calculus supplies `D_0`; a tie can be
resolved arbitrarily. Equations `(PDF5)--(PDF6)` then imply the reflection
identity by the exact factorization calculation.

For `(PDF7)`, the reflection defect of `C'` is at most `2delta`, because
both conjugation by `A` and inversion are isometries and `C` is exactly
reflected. Apply `(PDF2)`. For `(PDF8)`, insert and remove
`C'X'(C')^(-1)`; conjugation changes by at most twice the movement of its
conjugator. The cubic word bound is the three-term unitary telescoping
estimate.
