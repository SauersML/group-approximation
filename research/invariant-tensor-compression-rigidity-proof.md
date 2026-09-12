---
rg: 2
id: invariant-tensor-compression-rigidity-proof
kind: route
title: Instantiate the chain-condition principle on fixed subspaces
target: invariant-tensor-compression-rigidity
requires: [noetherian-invariant-compression-rigidity]
---

## Why sufficient

Write `rho_T` for the induced representation of `H` on `T(V)`; every listed
construction is functorial, so `rho_T` exists and
`T(V)^(h L h^{-1}) = rho_T(h) ( T(V)^L )` for all `h` — the equivariance of
fixed subspaces.

Take `P` to be the poset of linear subspaces of `T(V)` under inclusion,
with `H` acting through `rho_T`; finite-dimensionality gives the ascending
chain condition.  Set `I(L) = T(V)^L`.  Then `I` is **antitone** — a larger
subgroup fixes fewer tensors — and equivariant as above.  The antitone/ACC
case of `noetherian-invariant-compression-rigidity` gives
`rho_T(s) (T(V)^L) = T(V)^L`, and the left side is
`T(V)^(s L s^{-1})` by equivariance.

(Concretely the chain terminates for dimension reasons:
`T(V)^L <= T(V)^(s L s^{-1}) = rho_T(s) T(V)^L`, and an inclusion of
finite-dimensional spaces of equal dimension is an equality — the same one
line that proves `commutant-no-growth`.  The route through the principle
keeps the bookkeeping uniform across all constructions `T`.)
