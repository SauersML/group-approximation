---
rg: 2
id: thin-universal-fd-null-witness-proof
kind: route
title: Filter the finite-dimensional C-gap and kill the invariant sector with the outsider
target: thin-leak-has-universal-fd-null-laplacian-witness
requires:
  - sln-z-thin-codense-tau-pair
---

For every finite-dimensional representation `rho` of `A`, profinite
co-density gives

```text
H_rho^C=H_rho^A.                                       (1)
```

Bourgain--Varju expansion supplies `kappa>0` such that

```text
rho(Delta_C)|_((H_rho^A)^perp) >= kappa I.             (2)
```

The spectrum of `rho(Delta_C)` lies in `[0,L]`.  On the invariant part,
`rho(r)-1=0`.  On its orthogonal complement,

```text
||(1-rho(Delta_C)/L)^N||
 <= (1-kappa/L)^N=:q^N.                                (3)
```

Both subspaces are invariant under `rho(Delta_C)`, so

```text
||rho(y_N)||<=2q^N,                                    (4)

```

uniformly over `rho`, proving `(ULW2)`.

If `v` centralizes `pi(C)`, then it is fixed by every `alpha(c)`, hence
`alpha(Delta_C)v=0`.  Polynomial functional calculus gives
`alpha(x_N)v=v`, and multiplication by `alpha(r)-1` proves `(ULW3)` and
`(ULW4)`.
