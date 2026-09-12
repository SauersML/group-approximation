---
rg: 2
id: regular-stabilization-finite-corners-have-spectral-leakage
kind: claim
title: Nonamenability forces leakage from every finite corner of a regular stabilization
distinct_from:
  separate-return-models-do-not-force-a-common-base: that treats labeled diagonal orbit blocks and their Reiter boundary; this permits arbitrary non-diagonal finite-rank corners in any multiplicity amplification.
  sl3-homogeneous-ce-is-common-cocycle-spatialization: that is the unrestricted common-spatialization criterion; this rules out only finite-corner compression of the infinite regular Packer--Raeburn stabilization.
---

Let `Gamma` be finitely generated and nonamenable, let `S` be a finite
symmetric generating set, and let `lambda` be the left regular
representation.  There is `kappa_S>0` such that every nonzero finite-rank
projection `q` on `ell^2(Gamma) tensor K`, with arbitrary multiplicity
space `K`, satisfies

```text
sum_(s in S) ||(1-q)(lambda(s) tensor 1)q||_HS^2
  >= (kappa_S/2) Tr(q).                                  (RSF1)
```

Indeed, conjugation by `lambda` on Hilbert--Schmidt operators decomposes as
a direct sum of copies of `lambda`: the diagonal action on `Gamma x Gamma`
has orbits indexed by `x^(-1)y`.  Nonamenability therefore gives

```text
sum_s ||Ad(lambda(s))(T)-T||_HS^2
  >= kappa_S ||T||_HS^2.
```

Apply this to `T=q` and use, for equal-rank projections,

```text
||uqu^*-q||_HS^2=2||(1-q)uq||_HS^2.
```

For the cocompact lattice in the homogeneous-quotient lane, `(RSF1)` rules
out compressing the infinite Packer--Raeburn regular gauge to arbitrary
finite tracial corners with vanishing return leakage.  Finite quotient
regularizations avoid this spectral gap only by retaining their stabilizer
kernel cocycle.  This is a route-specific firewall, not a refutation of an
arbitrary non-Cartan common embedding.
