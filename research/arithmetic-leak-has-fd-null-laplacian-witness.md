---
rg: 2
id: arithmetic-leak-has-fd-null-laplacian-witness
kind: claim
title: Every arithmetic projective leak is detected by one finite-dimensional-null Laplacian sequence
distinct_from:
  thin-leak-has-universal-fd-null-laplacian-witness: that uses a profinitely dense thin subgroup of SL3(Z) and an outsider inside SL3(Z); this uses the co-dense lattice SL3(Z) inside SL3(Z[1/p]) and detects projective inner-adjoint leakage.
  projective-far-defect-formula: that computes one fixed far commutator defect; this packages every projective leak into an explicit sequence whose exact finite-dimensional norm decays exponentially.
---

Fix

```text
A=SL_3(Z[1/p]),             C=SL_3(Z),
h=diag(p,1,1/p),
```

and a finite symmetric generating set `S` of `C`.  Put

```text
Delta_C=sum_(s in S)(1-s)^*(1-s),
L=4|S|,
x_N=(1-Delta_C/L)^N,
y_N=(h-1)x_N in C[A].                                  (APW1)
```

There are `kappa>0` and `q=1-kappa/L<1` such that

```text
||y_N||_FD <= 2q^N,                                    (APW2)
```

where the supremum is over all exact finite-dimensional unitary
representations of `A`.  Indeed, property `(T)` gives the spectral gap on
the orthogonal complement of the `C`-fixed vectors.  Exact finite-dimensional
co-density gives `H^C=H^A`, so `h-1` kills the invariant sector and the
remaining sector contracts by `q^N`.

On the other hand, let `pi:A->U(M)` be a tracial representation and let a
unitary `U` projectively centralize `pi(C)`.  In the inner-adjoint matrix
realization put

```text
beta=Ad pi,              gamma=Ad beta,              T=Ad U.
```

The scalar projective phases disappear after the second adjoint, so `T` is
`C`-fixed and

```text
gamma(x_N)T=T,
||gamma(y_N)T||_2^2
 =2(1-|tau([U,pi(h)])|^2).                              (APW3)
```

Thus every projective transfer leak survives the same sequence `(y_N)` for
all `N`, although its norm in every exact finite-dimensional representation
decays exponentially.  Full temperedness or weak containment of the whole
selected cyclic module is stronger than the terminal input needed here.
