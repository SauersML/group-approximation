---
rg: 2
id: finite-positive-definite-window-relative-corner-proof
kind: route
title: Apply finite-group GNS and the multiplicative domain on the prescribed core
target: finite-positive-definite-window-is-a-relative-corner-selector
requires: []
---

A normalized `M_d`-valued positive-definite function `F` on the finite
group `G` defines a ucp map

```text
Theta:C^*(G)->M_d,       Theta(u_g)=F(g).
```

Its minimal Stinespring dilation `Theta(y)=V^*rho(y)V` has dimension at
most `d|G|`. For `b in B`, the equality
`Theta(u_b)=beta(b)` is unitary. Equality in both Kadison inequalities
puts `u_b` in the multiplicative domain, so
`rho(b)V=V beta(b)`. Compression gives
`V^*rho(s)V=F(s)`, and the prescribed Hilbert--Schmidt error bound follows
immediately. This proves the relative finite-corner selector directly; no
ambient residual finite-dimensionality input is used.
