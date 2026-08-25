---
rg: 2
id: regular-coset-displacement-hull-proof
kind: route
title: Flip the dihedral-fixed coset vector inside the regular Iwahori endpoint
target: displacement-carrier-has-p-fold-bs-hull
requires:
  - full-iwahori-relations-do-not-bound-unipotent-torsion
  - low-rank-reflection-surgery-preserves-the-exact-bs-core
---

Because `r,x in D_p`, left translation by either generator fixes the
normalized indicator of `D_p`.  Thus `Q_p` commutes with `lambda_p(r)` and
`Y_p`, proving `(DBH3)--(DBH4)` directly.

Let `U_1=lambda_p(s)^2` and `U_2=lambda_p(r s)`.  The tuples with reflections
`X_p` and `Y_p` use the same exact core, and `(Y_pU_i)^3=1`.  Telescope the
three occurrences of the reflection in

```text
(X_pU_i)^3-(Y_pU_i)^3.
```

Every summand is a unitary left/right translate of `X_p-Y_p=-2Q_p`.
Therefore each cubic residual has rank at most three and Frobenius norm at
most `3||2Q_p||_F=6`, proving `(DBH5)`.

The vectors `lambda_p(b)q_p` are normalized indicators of the left cosets
`bD_p`; they are equal exactly modulo `B_p intersect D_p` and otherwise
orthogonal.  In the standard projective matrix model, `D_p` is the
normalizer of the fourth-power split torus and its elements outside that
torus contain the Weyl factor, so they are not upper triangular.  Hence

```text
B_p intersect D_p=<r>.
```

The unipotent radical of `B_p` has order `p`, giving `(DBH6)`.  Since any
subspace reducing both core generators and containing `q_p` contains its
whole `B_p`-orbit, `(DBH7)--(DBH8)` follow.
