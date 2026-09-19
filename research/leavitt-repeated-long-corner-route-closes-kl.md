---
rg: 2
id: leavitt-repeated-long-corner-route-closes-kl
kind: route
title: Use the full-packet repeated tail as a nonsingular Leavitt equation
target: kl-violating-equation-over-leavitt-unit-group
requires:
  - leavitt-repeated-long-corner-template-kills-omega
  - leavitt-repeated-long-corner-full-packet-realization
---

Given the requested coefficients, form

```text
W=g_0t g_1t a t^(-1)c t g_4t b t^(-1)d t g_7t.
```

Its exponent sum is four.  The repeated-corner theorem puts the nonidentity
coefficient `x_15(s_0^2)=[c,d]` in the kernel of the coefficient map to
`<G,t|W=1>`.  Full packet generation makes this an equation over the explicit
finitely generated Leavitt elementary group, hence the required
Kervaire--Laudenbach violation.
