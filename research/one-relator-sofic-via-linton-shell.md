---
rg: 2
id: one-relator-sofic-via-linton-shell
kind: route
title: Answer Pestov 4.9 affirmatively by proving the finite rational-derived shell sofic
target: one-relator-groups-sofic
requires: [linton-shell-sofic, one-relator-soficity-localizes-at-rational-derived-stage]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

The main positive lane.  Given a one-relator group `G = F/<<w>>`, the reduction
supplies `n <= |w|` and `E = G_Q^(n)` with `G/E` solvable and

    E ≅ R ⋊_α F₀ ,   R = G_Q^(ω) = <<r>>_G ,   F₀ free .

If `E` is sofic then `G` is sofic, because a sofic kernel with amenable quotient
gives a sofic total group (Elek--Szabó), and `G/E` is solvable by the reduction.

That is the whole route.  Its content is entirely in the prerequisite
[[linton-shell-sofic]]; the second prerequisite is the already-established
reduction that produces the shell and certifies the amenability of the quotient.

The first derived quotient of the prerequisite is no longer open:
[[one-relator-fox-magnus-descent-to-derived-linton-radical]] proves `E/R'`
residually finite.  This does not complete the route, because arbitrary
extensions of a sofic group by a residually finite group need not be sofic.
What remains is an action-compatible approximation of the nonabelian core
`R'`, with the `k = 1` perfect regime as the essential case.

## Why this is a genuine reduction rather than a restatement

The two are equivalent — soficity of `G` implies soficity of its subgroup `E` —
so the route does not shrink the truth-value space.  What it shrinks is the
**object**.  The target quantifies over all one-relator presentations; the
prerequisite is a single structured group per presentation: free acting on
normally-one-generated rationally perfect, with the normal factor's
abelianization known exactly
([[linton-radical-abelianization-is-truncated-group-ring]]) and its acting factor
as far from Kazhdan as a group can be.

That distinction matters here in a way it usually does not, because the
alternatives on this claim are worse.  Every other lane either needs a
permanence theorem that is false ([[sofic-semidirect-product-closure-fails]]),
one that has been withdrawn
([[relative-soficity-extension-theorem-withdrawn]]), or one that nobody has
(amalgamation over nonamenable free edge groups, in
[[magnus-staggered-chain-sofic]]).

## Complete for the residually rationally solvable case

When `R = 1` the shell is free, hence sofic, and the route closes outright.
That special case is recorded separately as the established claim
[[residually-rationally-solvable-one-relator-sofic]], because it is a large
positive class and should not be reachable only through an open prerequisite.
