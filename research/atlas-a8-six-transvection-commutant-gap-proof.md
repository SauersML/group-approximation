---
rg: 2
id: atlas-a8-six-transvection-commutant-gap-proof
kind: route
title: Diameter-fifteen commutator telescoping and finite averaging give the regular-chart decoder
target: atlas-a8-six-transvection-commutant-gap
requires:
  - atlas-a8-six-transvection-normal-certificates
artifacts:
  - experiments/atlas_a8_transvection_normal_certificates.py
---

Write `lambda=lambda_k`.  The exact BFS audit used for the normal certificates
also records that every `g in A8` is a word

```text
g=s_1 ... s_l,       s_i in S,       l<=15.           (1)
```

For `||X||_op<=1`, commutator telescoping along `(1)` gives

```text
||[X,lambda(g)]||_2
 <= sum_(i=1)^l ||[X,lambda(s_i)]||_2
 <= 15 (sum_(s in S)||[X,lambda(s)]||_2^2)^(1/2).      (2)
```

Average over the finite regular action:

```text
E(X)=(1/|A8|) sum_(g in A8) lambda(g)Xlambda(g)^*.
```

`E` is the Hilbert--Schmidt orthogonal conditional expectation onto
`lambda(A8)'`.  Hence

```text
dist_2(X,lambda(A8)')
 <= ||X-E(X)||_2
 <= (1/|A8|) sum_g ||[X,lambda(g)]||_2.
```

Insert `(2)` to obtain `(A8-6COMM)`.  Neither the Cayley diameter nor finite
averaging depends on the external regular multiplicity `k`.
