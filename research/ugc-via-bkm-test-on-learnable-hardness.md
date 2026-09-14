---
rg: 2
id: ugc-via-bkm-test-on-learnable-hardness
kind: route
title: Dead -- prove 2-to-1 hardness on learnable-matching instances and feed the folded long-code noise test
target: unique-games-conjecture
requires: []
---

**Dead.** The attack: obtain NP-hardness of `Gap-2-to-1[1-eta, eta]` on
instances whose left-vertex matching families are learnable -- subexponential
and separated, e.g. affine, low-degree polynomial, or any bounded-description
algebraic enrichment of `F_lin` -- and then apply the folded long-code noise
test of Braverman--Khot--Minzer (ITCS 2021, Section 5) to reach unique games
hardness.

It is killed by `bkm-test-transparent-on-learnable-games`. On learnable
instances the decoder error `e(Psi)` is `o(1)`, so the test value is
`1/m+(1-1/m)rho^3 val(UG_der(Psi))^2 - o(1)`. For the test to be sound in the
NO case one needs `val(UG_der(Psi))` small there -- but then `Psi -> UG_der(Psi)`
is *already* a unique games hardness reduction, with constant alphabet and no
long code. The route therefore cannot prove more than its own input already
proves: it is transparent, not a genuine enrichment.

What survives is exactly the complement: instances whose matching families are
unlearnable (entropy linear in the alphabet, so full or near-full richness),
which is where `separated-small-pairing-families-defeat-the-noise-test` also
stops. That regime is the live target
`ugc-from-smooth-design-rich-2to1` / `smooth-design-rich-2to1-hardness`.
