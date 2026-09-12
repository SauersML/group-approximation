---
rg: 2
id: nonsofic-hyperbolic-via-hs-stable-kazhdan-hyperbolic
kind: route
title: A flexibly HS-stable Kazhdan hyperbolic group with b_2 >= 1 yields a non-hyperlinear hyperbolic finite central extension
target: nonsofic-hyperbolic-group
requires: [kazhdan-hyperbolic-hs-stability-kills-hyperlinearity, kazhdan-hyperbolic-b2-group-flexibly-hs-stable]
---

## Why sufficient

The open premise supplies `Γ`, and the established theorem supplies a finite
central extension `Γ_N` that is hyperbolic and not hyperlinear. Non-hyperlinear
groups are nonsofic.

This is a genuinely different lever from `nonsofic-hyperbolic-via-cheeger-threshold`.
That route's premise forces finite-residual behaviour of random groups, by
`finite-quotient-caps-cocycle-cheeger-constant`. The premise here is a unitary
rigidity property of a single hyperbolic Kazhdan group. It says nothing directly
about finite quotients, and it is consumed as rigidity for asymptotically
projective representations (Dogon--Vigdorovich).
