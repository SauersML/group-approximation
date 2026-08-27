---
rg: 2
id: paired-reservoir-via-renyi2-soft-covering
kind: route
title: Turn a uniform Renyi-2 rate gap into the same-reservoir boundary dichotomy
target: paired-same-reservoir-boundary-lemma
requires:
  - renyi-soft-covering-rate-floor
  - dual-prefix-renyi2-rate-gap
---

Use the dual-prefix rate compiler to encode the address as `X`, the available
multiplicity reservoir as `E`, and normalized-HS boundary leakage as the
order-two covering divergence.  The uniform inequality
`R<=I_2(X:E)-epsilon`, together with the exact strong-converse exponent,
forbids asymptotically successful covering unless the two branch maps close
on the same reservoir.  Failure of covering pays the boundary term by clause
1 of the rate compiler.  These are exactly the two alternatives required by
`paired-same-reservoir-boundary-lemma`.
