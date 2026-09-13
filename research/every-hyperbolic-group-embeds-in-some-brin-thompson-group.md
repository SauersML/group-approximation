---
rg: 2
id: every-hyperbolic-group-embeds-in-some-brin-thompson-group
kind: claim
title: Every hyperbolic group embeds in some Brin-Thompson group nV
---

For every finitely generated word-hyperbolic group `G` there is `n ≥ 1` and an
injective homomorphism `G → nV`. This is the affirmative answer to Zaremsky
Problem 2.19(a) (`zaremsky-2-19a-every-hyperbolic-group-in-some-nv-resolved`).

## Known cases

- **Virtually special groups.** Every virtually special group embeds in some nV
  (Belk–Bleak–Matucci, arXiv:1602.08635, Corollary 1.5). This includes every
  hyperbolic group acting properly and cocompactly on a CAT(0) cube complex, by
  Agol's theorem. Examples: finite-volume hyperbolic 3-manifold groups, finite
  `C'(1/6)` small cancellation groups, one-relator groups with torsion and
  hyperbolic Coxeter groups.
- **Virtual subgroups of RAAGs.** Every group that virtually embeds in a
  finitely generated RAAG embeds in some nV (same source, p. 2). This includes
  hyperbolic subgroups of such groups that are not themselves cubulated.

## Consequence if true

Infinite hyperbolic groups with property (T) exist
(`torsion-free-hyperbolic-kazhdan-partner-exists`). So this claim would put an
infinite Kazhdan group inside some mV, and then kV lacks the Haagerup property
for every k ≥ m. That is a negative answer to the Haagerup part of Zaremsky
Problem 2.7.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv): the cubulated case is imported. Every
  hyperbolic group that virtually embeds in a RAAG has the Haagerup property, so
  the known method cannot reach infinite hyperbolic Kazhdan groups. A proof must
  build faithful actions of Kazhdan hyperbolic groups on the Cantor cube by
  piecewise prefix replacements.
  - The natural candidates fail, because their local maps have nontrivial
    states: the boundary action is rational but not piecewise canonical
    (Belk–Bleak–Matucci, arXiv:1711.08369), and so are actions on
    Bruhat–Tits flag varieties.
  - No construction is known to this lane. Such a construction would also
    decide the Haagerup part of Problem 2.7 negatively, so expect it to be hard.
