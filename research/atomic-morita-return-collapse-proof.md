---
rg: 2
id: atomic-morita-return-collapse-proof
kind: route
title: Cut a surviving torsion spectrum and apply the one-third atomic gap coordinatewise
target: atomic-morita-return-kills-finite-order-mf-mark
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

Let `rho:Gamma->U(Q_d)` be a norm-matrix-corona homomorphism and suppose
`rho(w)!=1`.  Choose unitary lifts of the finitely many presentation
generators.  Their relator defect `delta_n` tends to zero.

The finite-order relation for `w` permits dimension-independent spectral
rounding of `w(U_n)` to an exact finite-order unitary.  Since `rho(w)!=1`,
after passing to a subsequence one fixed nontrivial spectral value has a
nonzero spectral projection `p_n` at every coordinate.  No density statement
is inferred or needed.

AMR supplies four corner operators for which the three binary Leavitt
defects are at most `eta(delta_n)`.  The atomic gap gives at every coordinate

```text
1
 <= ||t_(0,n)s_(0,n)-p_n||_op
    +||t_(1,n)s_(1,n)-p_n||_op
    +||s_(0,n)t_(0,n)+s_(1,n)t_(1,n)-p_n||_op
 <= 3 eta(delta_n).
```

The right side tends to zero, a contradiction.  Thus every corona
homomorphism kills `w`, proving `(AMR2)`.  If `w` normally generates, the
normal kernel of every corona homomorphism is the whole group, proving
`(AMR3)`.

