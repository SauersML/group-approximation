---
rg: 2
id: diagonal-retention-fusion-coefficient-proof
kind: route
title: Compute the maximal fusion weight by positive-functional domination
target: diagonal-retention-fusion-coefficient
requires:
  - fixed-density-polarization-retention-is-terminal
---

For positive functionals `sigma,tau` on a unital star algebra, the largest
`beta` for which `sigma-beta tau` is positive is

```text
inf_(tau(a*a)>0) sigma(a*a)/tau(a*a).
```

Apply this with `sigma=tau^n`.  The test element `a=1` shows the infimum is
at most one.  If `beta<1`, positivity of `tau^n-beta tau`, together with its
value `1-beta` at the identity, makes

```text
rho=(tau^n-beta tau)/(1-beta)
```

a normalized positive-definite central function, hence a character.  The
converse is immediate from a convex decomposition.  Expanding `a*a` gives
the finite Gram formula `(DRC3)`.

For every fixed `a`, pointwise convergence `(DRC4)` gives

```text
tau^(n_k)(a*a)/tau(a*a)
 -> phi_H(a*a)/tau(a*a).
```

Taking the infimum first and then the limsup proves `(DRC5)`.  If
`d_infty>0`, choose `0<beta<d_infty`; then `beta tau<=phi_H`.
For completeness, no compactness of finite-stage densities is being assumed
here.  Domination first makes `tau` vanish on the null ideal of `phi_H`, so it
extends normally to `L(G/H)`.  Noncommutative Radon--Nikodym gives a bounded
density `0<=h<=beta^(-1)` there.  Since both functionals are traces, `h` is
central.  The `tau` GNS algebra is therefore the support central summand
`s(h)L(G/H)`, equipped with the central density `h`; in particular CE of
`L(G/H)` implies CE of `tau`.  This is the central-domination step isolated
in `fixed-density-polarization-retention-is-terminal`.  Therefore a non-CE
`tau` and CE `L(G/H)` force `d_infty=0`, and `(DRC5)` forces `(DRC6)`.
