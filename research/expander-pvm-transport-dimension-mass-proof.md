---
rg: 2
id: expander-pvm-transport-dimension-mass-proof
kind: route
title: Apply Poincare to square roots of spectral ranks
target: expander-pvm-transport-forces-dimension-or-mass-collapse
requires: []
---

Write `N=|Omega|` and `f(v)=sqrt(p_v)`.  For projections `P,Q` and a unitary
`W`, normalized-trace Cauchy--Schwarz gives

```text
tr_d(W P W^* Q) <= sqrt(tr_d(P) tr_d(Q)).
```

Therefore

```text
||W P W^*-Q||_2^2
 =tr_d(P)+tr_d(Q)-2 tr_d(W P W^*Q)
 >=(sqrt(tr_d(P))-sqrt(tr_d(Q)))^2.                            (1)
```

Apply `(1)` to every colored edge in `(EP1)`.  With the convention that
`E_(v,s)` is the uniform oriented-edge average,

```text
E_PVM >= N E_(v,s) |f(v)-f(sv)|^2.                            (2)
```

The Hilbert-valued Poincare inequality (here scalar-valued is enough) says

```text
E_(v,s)|f(v)-f(sv)|^2
 >=2 gamma (E_v f(v)^2-(E_v f(v))^2).                         (3)
```

At most `d` of the projections are nonzero, since nonzero pairwise
orthogonal subspaces in `C^d` have total rank at most `d`.  Hence
Cauchy--Schwarz on the support of `f` gives

```text
(E_v f(v))^2
 <=(d/N) E_v f(v)^2.                                          (4)
```

Finally `E_v f(v)^2=mu/N`.  Substitute `(3)--(4)` into `(2)` to obtain

```text
E_PVM >=2 gamma mu(1-d/N),
```

which is `(EP2)`.  If `d<N/2`, then `(EP3)` follows.

