---
rg: 2
id: matrix-corona-k0-index-survives-proof
kind: route
title: Six-term sequence again, in the other degree
target: matrix-corona-k0-index-survives
requires: []
---

## Why sufficient

Apply the six-term exact sequence to
`0 -> oplus M_{d_n} -> prod M_{d_n} -> Q -> 0` in the remaining degree:

    K_0(oplus) -> K_0(prod) -> K_0(Q) -> K_1(oplus).

`K_1(oplus_n M_{d_n}) = 0`, since `K_1` commutes with the `c_0`-direct sum
and each `K_1(M_{d_n})` vanishes.  So `K_0(prod) -> K_0(Q)` is surjective
with kernel the image of `K_0(oplus)`.  As computed in
`matrix-corona-k1-vanishes-proof`, `K_0(oplus) = oplus Z` and
`K_0(prod) = prod Z` by coordinatewise rank, with the inclusion as the
connecting map.  Hence `K_0(Q) = prod Z / oplus Z`.

The stability statement is the standard one: the Bott index of a pair of
unitaries with commutator smaller than a universal constant is locally
constant in the pair, so a perturbation of a representing sequence by a
sequence tending to zero leaves every sufficiently late term unchanged, and
the class in `prod Z / oplus Z` is unchanged.
