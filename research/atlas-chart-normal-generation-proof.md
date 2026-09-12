---
rg: 2
id: atlas-chart-normal-generation-proof
kind: route
title: Quotient by one chart element and apply chart injection
target: atlas-chart-elements-normally-generate-six-relator-group
requires:
  - atlas-six-relator-nontrivial-quotients-inject-charts
  - atlas-six-relator-hyperlinear-escape-test
---

Fix `1 != a in A8_1` and let

```text
q:Gamma_6 -> Gamma_6/<<a>>
```

be the quotient map.  The restriction of `q` to `A8_1` has nontrivial
kernel.  Since `A8` is simple, that restriction is trivial.  But
`atlas-six-relator-nontrivial-quotients-inject-charts` says that every
nontrivial quotient restricts injectively to both charts.  Therefore `q` is
trivial and `<<a>>=Gamma_6`.  The second chart is identical.

Now fix one nonidentity chart word `t`.  If `t` survives under a homomorphism
to a tracial matrix ultraproduct, the image is a nontrivial hyperlinear
quotient.  Conversely, any nontrivial hyperlinear quotient injects the first
chart and hence retains `t`.  Together with
`atlas-six-relator-hyperlinear-escape-test`, this is precisely the fixed-word
version of the remaining matrix-ultraproduct escape.
