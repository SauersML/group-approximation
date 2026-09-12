---
rg: 2
id: non-rf-hyperbolic-via-periodic-higman
kind: route
title: Fill the periodic-Higman torus at one omitted prime period
target: non-residually-finite-hyperbolic-group
requires:
  - periodic-higman-period-spectrum-criterion
  - periodic-higman-large-prime-period-gap
---

Choose the prime `ell>=m_0` supplied by the period-gap claim.  Because `ell`
is prime, the only divisors of `ell` are `1` and `ell`; by definition every
member of `Sigma` is greater than one.  Thus no member of `Sigma` divides
`ell`.  Applying the period-spectrum criterion with `m=ell` makes

```text
G_ell=<a,b,c,d,t |
  t x_i t^(-1)=[x_i,x_(i-1)], t^ell=1>
```

word-hyperbolic and not residually finite.  No conclusion follows until the
open period-gap premise is proved.
