---
rg: 2
id: toeplitz-self-embedding-fixes-unbounded-congruence-types
kind: claim
title: The proper Toeplitz self-embedding fixes irreducible congruence types of unbounded degree
distinct_from:
  packet-headed-toeplitz-shift-is-schur-type-preserving: that proves stationarity on the finite forbidden coefficient blocks inside the infinite Toeplitz ring; this constructs unbounded old-group irreducible types on which the entire proper endomorphism becomes the identity.
  finite-normalizer-covariance-density-no-go: that dilutes commutant density with regular semidirect quotients for finite automorphism covariance; this uses the genuinely one-sided Toeplitz endomorphism itself and irreducible finite-field quotient types.
  regular-trace-forbids-universal-bounded-type-placement: that uses the infinite regular representation to rule out a universal projection inclusion; this gives exact finite-dimensional ascending-HNN representations with zero bounded-type mass and vanishing adjoint commutant density.
---

Let

```text
T=F_2<x,y | yx=1>,
sigma(a)=xay+epsilon(a)(1+xy),
Gamma=EL_r(T),
alpha=EL_r(sigma),                                      (TUC1)
```

where `r>=3` is in the property-`(T)` range used by the Toeplitz
compressor.  For every `K` there is a finite-dimensional irreducible unitary
representation `rho_K` of `Gamma` such that

```text
dim(rho_K)>K,                 rho_K o alpha=rho_K.       (TUC2)
```

Consequently `rho_K` extends to the ascending HNN group

```text
<Gamma,t | t g t^-1=alpha(g)>
```

by `rho_K(t)=1`.  If `p_<=K` is the bounded-type central projection from
`kazhdan-bounded-types-form-central-summand`, then

```text
rho_K(p_<=K)=0,
dim End_Gamma(rho_K)/dim(rho_K)^2=1/dim(rho_K)^2 -> 0.   (TUC3)
```

Thus non-surjectivity of the Toeplitz coefficient map, even together with
exact stable-letter transport, does not force any positive bounded-type
mass.  In these escape representations the Toeplitz defect `1+xy` is zero.
Accordingly this does not refute a conditional estimate whose input is
positive forbidden-head mass; it proves that such an estimate must use that
positive mass to exclude congruence collapse.  Stationarity under the
one-sided transport alone cannot supply the missing estimate.
