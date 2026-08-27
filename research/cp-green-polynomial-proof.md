---
rg: 2
id: cp-green-polynomial-proof
kind: route
title: Sum the code-noise and equality-walk semigroups for finitely many steps
target: code-laplacian-has-uniform-cp-green-approximants
requires:
  - complete-overlay-code-group-has-uniform-conjugation-gap
---

On a matrix block from code character `chi` to code character `psi`, each
`E_i` has eigenvalue one if `chi_i=psi_i` and zero otherwise.  Hence `A` has
eigenvalue

```text
1-wt(chi+psi)/L.
```

The eigenvalue is one on the common commutant and at most `1-delta`
elsewhere.  This proves `(CLG4)`.  The finite geometric-series identity
gives `(CLG3)`.

Every `A^t` is ucp.  Amplifications of a ucp map contract operator columns
and rows, so their sum has the asserted bound `K`.  For equality clouds, a
doubly stochastic Markov average is row-contractive by operator Jensen:
if `Y_i=sum_j p_ijX_j`, then

```text
sum_i Y_i^*Y_i <=sum_(i,j)p_ij X_j^*X_j=sum_jX_j^*X_j,
```

and similarly for columns.  Laziness and the expander gap give the stated
mean-zero `L_2` decay, completing the parallel Green construction.
