---
rg: 2
id: fpbs-split-product-metric-needs-finite-conjugacy-orbits-proof
kind: route
title: Left multiplication by the complement twists the normal coordinate by conjugation
target: fpbs-split-product-metric-needs-finite-conjugacy-orbits
requires: []
---

Written proof.
* For `h_0` in `H`, `h_0 (n h) = (h_0 n h_0^-1)(h_0 h)`, so left
  multiplication by `h_0` acts on the normal coordinate by conjugation.
* Apply invariance of `rho` to two elements `n h` and `n' h` with the same
  `H`-coordinate. It gives
  `l_N((h_0 n h_0^-1)^-1 (h_0 n' h_0^-1)) = l_N(n^-1 n')`, that is,
  `l_N(h_0 k h_0^-1) = l_N(k)` for `k = n^-1 n'`.
* Every `k` in `N` arises this way, so `l_N` is `H`-conjugation invariant.
* So the `H`-orbit of `k` lies in the `l_N`-ball of radius `l_N(k)`, which is
  finite. QED

The Burnside instance in the claim uses only the cyclic, hence finite,
centralizers of `fpbs-burnside-embedding-input` and the infinitude of `B(m-1,n)`.
This is dependency bookkeeping for a written deduction, not a formal
verification.
