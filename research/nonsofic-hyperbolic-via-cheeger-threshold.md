---
rg: 2
id: nonsofic-hyperbolic-via-cheeger-threshold
kind: route
title: Chapman--Peled Theorem 1.1 with its exact threshold hypothesis
target: nonsofic-hyperbolic-group
requires: [random-complex-cocycle-cheeger-beats-triangle-count]
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

Chapman--Peled, arXiv:2509.21566v2, Theorem 1.1 (p. 2), read from the PDF: if
a.a.s. `h_1(Y,Sym) = ω(n^(-3)p^(-1))` for `p = n^(-1+η)`, `0<η<1/2`, then
`π_1(Y)` is a.a.s. a non-sofic hyperbolic group. The implication is proved in
their §4.2. The artifact gives the steps, and the soficity-free part is extracted as
`finite-quotient-caps-cocycle-cheeger-constant`.

This supersedes `cocycle-stability-nonsofic-route` as the precise record. That
route asks for a constant lower bound, which only feeds the present premise.

The Glebsky--Rivera step (their Proposition 2.8) concerns *flexible*
homomorphism stability, obtained from `h_1 > 0` through their Fact 2.4. Strict
Becker--Lubotzky instability of infinite sofic Kazhdan groups does not apply to
flexible stability, so it cannot shortcut the triangle argument.
