---
rg: 2
id: two-masa-whole-face-sign-obstruction-proof
kind: route
title: Alternate spectral signs between two nonorthogonal MASAs
target: whole-face-sign-rounding-does-not-inherit-gap-contraction
requires:
  - random-whole-face-pinchings-contract-transverse-l2
---

Because `Phi` is the orthogonal projection onto the face commutant,
`B-Phi(B)` is orthogonal to that commutant.  Scalar functional calculus for
the self-adjoint contraction `X=Phi(B)` gives

```text
||X-sgn(X)||_2^2 <= tr(1-X^2)=||B-X||_2^2.
```

The two differences are orthogonal, proving `(WFS1)`.  Apply the squared
three-term triangle inequality to

```text
B_1'-B_2'=(B_1'-B_1)+(B_1-B_2)+(B_2-B_2')
```

and then `(WFS1)` to obtain `(WFS2)`.

For the obstruction take `A=Z` and
`C=cos(phi)Z+sin(phi)X`.  On traceless Bloch space `Phi_A` and `Phi_C` are
the orthogonal projections onto their two axes.  The largest eigenvalue of
their average is `(1+cos(phi))/2`, proving `(WFS3)`.  Moreover

```text
Phi_A(C)=cos(phi)A,       Phi_C(A)=cos(phi)C,
```

and `cos(phi)>0`, proving `(WFS4)`.  Both `A` and `C` have trace zero and
normalized `L_2` norm one, hence remain at squared distance one from the
scalar common fixed space after every update.
