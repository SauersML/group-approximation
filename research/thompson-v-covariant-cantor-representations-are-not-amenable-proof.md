---
rg: 2
id: thompson-v-covariant-cantor-representations-are-not-amenable-proof
kind: route
title: An invariant state on B(H) restricts to an invariant measure, and cylinders halve
target: thompson-v-covariant-cantor-representations-are-not-amenable
requires: []
---

If `pi` is Bekka-amenable, there is a state `Phi` on `B(H)` with
`Phi(pi(g) T pi(g)^*) = Phi(T)` for all `T` and `g`. Covariance gives
`Phi(rho(f o g^(-1))) = Phi(rho(f))`, so `Phi o rho` is a `V`-invariant state on
`C(X)`, a `V`-invariant Radon probability `mu` on the Cantor set.

The prefix replacements `{0,10,11} -> {00,01,1}` and `{0,10,11} -> {01,00,1}` map the
cylinder `0*` onto `00*` and onto `01*`. So `mu(0*) = mu(00*) + mu(01*) = 2 mu(0*)`,
giving `mu(0*) = 0`, and likewise `mu(1*) = 0`, a contradiction.

The finite-rank formulation is standard. By Bekka, amenability of `pi` is
equivalent to almost invariant vectors in `pi (x) conj(pi)`, the conjugation
action on Hilbert--Schmidt operators. Taking absolute values and spectral
cut-offs of an almost invariant Hilbert--Schmidt operator gives the displayed
almost invariant finite-rank projections.
