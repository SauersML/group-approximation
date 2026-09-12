---
rg: 2
id: subexponential-blr-scalar-escape-proof
kind: route
title: Count the extendible parity-code dimension against character Hamming balls
target: subexponential-blr-sampling-has-scalar-contextual-escape
requires: []
---

Write every sign as `(-1)^u`.  The tester becomes a consistent affine linear
system over `F_2` in `K+p` variables with at most `m` equations.  Its solution
set `S` is an affine space of dimension at least `K+p-m`.  Projection to the
`K` selected coordinates has kernel dimension at most `p`, so the set `T` of
extendible tables is an affine subspace with

```text
dim T >= K-m.                                             (SBS3)
```

There are at most `2^r` distinct restrictions of additive characters to the
selected labels.  A Hamming ball of radius `rho K` in `F_2^K` contains at
most

```text
sum_(j<=rho K) binom(K,j) <= 2^(H_2(rho)K)                (SBS4)
```

points.  If every member of `T` were within `rho q` of some character, then

```text
2^(K-m) <= |T|
         <= 2^r 2^(H_2(rho)K),                           (SBS5)
```

contradicting `(SBS1)`.  Hence one extendible table lies outside all those
balls and, by definition of `T`, extends to an exact assignment of every
auxiliary sign.

For `rho=1/4`, `H_2(1/4)<7/8`, so `(SBS2)` implies `(SBS1)`.  Ordinary BLR
checks `f(a)f(b)=f(a+b)` and every scalar restriction of a group-word
same-basis parity packet are among these affine equations.
