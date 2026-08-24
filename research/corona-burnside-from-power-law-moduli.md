---
rg: 2
id: corona-burnside-from-power-law-moduli
kind: route
title: Feed the dimension-free moduli into the established corona equivalence
target: operator-norm-restricted-burnside
requires:
  - matrix-restricted-burnside-gap
  - corona-restricted-burnside-equals-power-law-moduli
---

Fix `m` and `N`. `matrix-restricted-burnside-gap` is exactly clause `(B)` of
`corona-restricted-burnside-equals-power-law-moduli`, in its sharpened form
with the single threshold `eps = delta_N`. That established equivalence
gives clause `(A)`: every `m`-generated subgroup of `U(Q)` of exponent
dividing `N` is finite, for every norm matrix corona `Q`.

A finitely generated subgroup of finite exponent is `m`-generated of exponent
dividing `N` for some `m, N`, so quantifying the above over all pairs `(m,N)`
gives the target.

**Why the equivalence is carried as a prerequisite rather than cited in
prose.**  The direction used here is `(B) => (A)`, which is where the
finiteness of the word set `W` and the finiteness of `R(m,N)` are spent. The
converse direction `(A) => (B)` is not used by this route, but it is what
makes the remaining hole honest rather than merely sufficient: by the
constructive contrapositive recorded in the equivalence, a failure of
`matrix-restricted-burnside-gap` does not just break this route, it builds an
exponent-`N` corona subgroup escaping `R(m,N)` and so refutes the target
outright. This route therefore sits on a genuine fork, and no second route
is written for the converse -- a second route would create a spurious
dependency cycle for a fact the established claim already carries.
