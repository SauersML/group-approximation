---
rg: 2
id: fpbs-farber-excludes-bounded-exponent-certificates
kind: claim
title: A group with a Farber chain has only locally finite bounded-exponent subgroups, so bounded-centralizer cost certificates never apply inside it
distinct_from:
  fg-rf-bounded-exponent-groups-are-finite: that is restricted Burnside for one finitely generated residually finite group; this applies it to every subgroup of a group carrying a Farber chain and reads off the failure of the Donoso-Echenique--Silva finite-cost hypothesis.
  fpbs-bounded-centralizer-relative-cost: that proves relative cost zero under uniformly bounded centralizers; this shows no infinite finitely generated group with a Farber chain satisfies or contains a subgroup satisfying that hypothesis, so it cannot be combined with Abert-Nikolov.
  bounded-exponent-fg-group-residual-has-finite-index: that constructs the finite residual of a bounded-exponent group; this is about residually finite ambient groups and their bounded-exponent subgroups.
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

Let `G` be an infinite finitely generated group with a Farber chain. Then:

1. `G` is residually finite.
2. Every bounded-exponent subgroup of `G` is locally finite.
3. Let `M` be any group with `|C_M(g)| <= n` for all `g != e`. No subgroup of
   `M` that is also a subgroup of `G` contains an infinite finitely generated
   subgroup. So Donoso-Echenique--Silva Proposition 2.7 ("Let N be a subgroup
   of G that contains an infinite finitely generated subgroup. Then
   cost(N)<∞", under the centralizer bound) applies to no subgroup of `G`.
4. `G` does not have uniformly bounded centralizers.

The step where the bounded-centralizer torsion certificate dies against the
profinite Abert--Nikolov lower bound is its hypothesis "contains an infinite
finitely generated subgroup". The invariant is bounded exponent, forced by
`<g> <= C_M(g)`.
