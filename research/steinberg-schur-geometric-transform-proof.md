---
rg: 2
id: steinberg-schur-geometric-transform-proof
kind: route
title: Sum the corrected Pascal and antidiagonal rows by geometric weights
target: steinberg-schur-geometric-row-transform
requires:
  - steinberg-schur-corrected-endpoint-reduction
---

Apply `(SGT3)` to the Pascal tail and subtract its diagonal and three missing
top endpoints.  Substitute `k=p-j` in the corrected antidiagonal and use the
binomial theorem after removing `k=0,1,2`; adding the two expressions gives
`(SGT2)`.  Direct unsimplified summation gives `(SGT5)` and the two boundary
columns.  Dividing by `s` leaves four pure exponentials plus a polynomial
with nonzero quadratic coefficient, so the confluent Vandermonde argument on
seven consecutive columns proves the one-weight firewall.
