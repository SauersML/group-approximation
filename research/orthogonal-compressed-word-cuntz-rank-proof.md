---
rg: 2
id: orthogonal-compressed-word-cuntz-rank-proof
kind: route
title: Count each compressed branch kernel and test universal fullness in the regular factor
target: orthogonal-compressed-word-branches-have-cuntz-rank-floor
requires: []
---

The positive contraction `A_i=X_i^*X_i` acts on `EH` and has

```text
rank(A_i)=rank(X_i)<=rank(Q_i).                        (OCP1)
```

Consequently its kernel inside `EH` has dimension at least
`rank(E)-rank(Q_i)`.  On that kernel, `A_i-E=-I`, so

```text
||X_i^*X_i-E||_2^2>=tr_d(E)-tr_d(Q_i).                (OCP2)
```

Summing `(OCP2)` and using orthogonality, hence
`sum_i Q_i<=E`, proves `(OCB2)`.

For infinite completeness, infinite stabilization makes the source, every
child, and their ambient complements countably infinite.  Choose a unitary
between `EH` and `Q_iH` and independently a unitary between their
complements.  Their direct sum is the required ambient `U_i`, and its
compression has initial Gram `E`.

Finally apply `(OCB2)` to the left regular representation.  Universal
source-fullness makes its left side zero.  For `k>=2`, the right side forces
the faithful regular trace of `E` to vanish.  A nonzero projection in the
embedded finite packet algebra remains nonzero in `M_n(L(Gamma))`, giving
the claimed contradiction.
