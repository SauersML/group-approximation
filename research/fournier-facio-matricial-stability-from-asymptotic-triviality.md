---
rg: 2
id: fournier-facio-matricial-stability-from-asymptotic-triviality
kind: route
title: Asymptotic triviality implies matricial stability
target: fournier-facio-group-matricially-stable
requires: [fournier-facio-asymptotic-representations-trivial]
---

## Proof

For an arbitrary operator-norm asymptotic homomorphism
`phi_n : G -> U(k_n)`, take the genuine representations

`rho_n(g) = 1_{k_n}`.

By `fournier-facio-asymptotic-representations-trivial`, for every fixed
`g : G` one has `||phi_n(g) - rho_n(g)|| -> 0`.  This is exactly the
pointwise operator-norm correction demanded by matricial stability.
