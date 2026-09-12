---
rg: 2
id: atlas-a8-four-cycle-commutant-gap-proof
kind: route
title: Diameter-seventeen telescoping and A8 averaging give the minimal transvection decoder
target: atlas-a8-four-cycle-commutant-gap
requires:
  - atlas-a8-minimal-four-transvection-cycle
---

Write `lambda=lambda_k`.  By the exact four-cycle audit, every `g in A8` has a
directed word

```text
g=t_1...t_l,       t_i in T,       l<=17.
```

Hence for `||X||_op<=1`, commutator telescoping gives

```text
||[X,lambda(g)]||_2
 <= 17 (sum_(t in T)||[X,lambda(t)]||_2^2)^(1/2).
```

Average `X` over the finite regular action.  The map

```text
E(X)=(1/|A8|) sum_g lambda(g)Xlambda(g)^*
```

is the Hilbert--Schmidt orthogonal conditional expectation onto
`lambda(A8)'`, so

```text
dist_2(X,lambda(A8)')
 <= (1/|A8|) sum_g ||[X,lambda(g)]||_2.
```

Combining the two displays proves `(A8-4COMM)`.  The argument and constant are
unchanged by regular amplification.
