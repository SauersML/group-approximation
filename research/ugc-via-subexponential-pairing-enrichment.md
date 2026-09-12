---
rg: 2
id: ugc-via-subexponential-pairing-enrichment
kind: route
title: Dead -- enrich F_lin to a separated family of subexponential size and apply the folded long-code noise test
target: unique-games-conjecture
requires: []
---

**Dead.** The attack: Braverman--Khot--Minzer (ITCS 2021, Section 1.3) float a
chain `F_lin = F_0 <= F_1 <= ... <= F_T = F_all` of pairing families. The
natural shortcut stops at an intermediate stage `F_j`: pairings given by affine
or low-degree polynomial involutions, or any other algebraic enrichment of
`F_lin`. It would prove hardness of `F_j`-rich 2-to-1 games and then feed them
to the folded long-code noise test of their Section 5, obtaining unique games
hardness.

It is killed by `separated-small-pairing-families-defeat-the-noise-test`. For
every `delta_0`-separated family with `log |F_j| <= (rho^4 delta_0^2/96 - c) N`,
there are `F_j`-rich source games of vanishing value whose output unique games
have value at least `rho^3 - o(1)`. So the test is not sound on such inputs.
Bounded-description algebraic families are separated and have size
`2^(polylog N)`.

What survives: the chain itself, applying the test only at full richness, and
enrichment to families of exponential size with near-duplicate structure, which
the obstruction does not cover.
