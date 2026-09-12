---
rg: 2
id: locally-finite-checksum-multiplicity-simplex-proof
kind: route
title: Align cross-amplified restrictions through a finite-subgroup multiplicity simplex
target: locally-finite-checksum-misses-all-fd-types
requires: []
---

Choose `N` with

```text
4 sum_(n>=N)a_n < epsilon/2,                            (1)
```

and put `K=<m_0,...,m_(N-1)>`.  Local finiteness makes `K` finite.  For a
finite-dimensional representation `rho` of `M`, decompose

```text
rho|_K ~= direct_sum_(tau in Irr(K)) tau^(direct_sum c_tau(rho))
```

and record its normalized Hilbert-space multiplicity vector

```text
p_tau(rho)=c_tau(rho) dim(tau)/dim(rho).                (2)
```

The vector `p(rho)` lies in the fixed finite-dimensional probability
simplex on `Irr(K)`.  Compactness gives distinct `rho,sigma in Omega` with

```text
||p(rho)-p(sigma)||_1 < eta,                            (3)
```

where `eta>0` will be chosen below.

Let `d=dim(rho)` and `e=dim(sigma)`.  On restriction to `K`, the two
`de`-dimensional cross-amplifications in `(LFC2)` contain respectively

```text
e c_tau(rho),              d c_tau(sigma)               (4)
```

copies of `tau`.  Conjugate them so that the minimum of the two
multiplicities is paired identically for every `tau`.  The total unpaired
Hilbert-space dimension, divided by `de`, is exactly

```text
sum_tau dim(tau)|e c_tau(rho)-d c_tau(sigma)|/(de)
 = ||p(rho)-p(sigma)||_1 < eta.                         (5)
```

Every `g in K` acts identically on the paired subspace.  On its orthogonal
complement both actions are unitary, so

```text
||rhohat(g)-sigmahat(g)||_(2,de)^2 <= 4 eta.            (6)
```

Choose `eta` so that `4 eta sum_(n<N)a_n<epsilon/2`
(with no condition needed if this finite sum is zero).  Equations `(1)` and
`(6)`, together with the universal squared unitary diameter `4` on the
tail, prove `(LFC3)`.

Because `rho` and `sigma` are inequivalent irreducibles of `M`, their
cross-amplifications remain two distinct isotypic representations.  The
equal-dimensional block swap therefore exchanges their central isotypic
projections, giving transport energy `2`; the block calculation from
`summable-noncommutative-checksum-compactness-proof` gives the covariance
energy `(LFC3)`.
