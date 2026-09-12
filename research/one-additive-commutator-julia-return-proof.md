---
rg: 2
id: one-additive-commutator-julia-return-proof
kind: route
title: Take the trace of one commutator residual and insert the heat bound
target: one-additive-commutator-suffices-for-julia-return
requires:
  - fanizza-heat-filter-has-uniform-cstar-decay
---

For `(ACJ1)`, subtract the two product residuals and use the triangle
inequality.  For the strictly weaker hypothesis `(ACJ3)`, normalized trace
has Hilbert--Schmidt norm one and `tr([Y_t,X_t])=0`, hence

```text
|tr(P)-tr(A_t)|<=omega(Def).
```

The accelerated heat estimate gives
`0<=tr(A_t)<=C_m/(4t^2)`, proving `(ACJ4)`.

For the sharp converse `(ACJ5)`, subtract the scalar part of the target.
The zero-diagonal basis induction and the explicit diagonal commutator
given in the claim show that the remaining traceless matrix is one
commutator.  Orthogonality of the scalar and traceless subspaces gives the
claimed exact distance.

For the bounded self-adjoint refinement, greedily alternating the signs of
the real eigenvalues keeps every partial sum within the largest eigenvalue
modulus.  Direct multiplication of the weighted cyclic shift and its
inverse shift gives `(ACJ7)`, and subtracting the scalar part costs at most
a factor two in operator norm.

Finally the two standard Steinberg commutator identities in `(ACJ9)` and
root-subgroup additivity give `e_13(YX-XY)`.  In a standard `3 by 3`
realization its only nonzero difference block is the `(1,3)` coefficient;
normalizing the block trace proves `(ACJ10)`.
