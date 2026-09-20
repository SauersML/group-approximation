---
rg: 2
id: fpbs-cost-betti-for-finitely-presented-groups
kind: claim
title: Bernoulli cost equals one plus the first L2 Betti number for every infinite finitely presented group
distinct_from:
  fpbs-bernoulli-cycle-tail-compactness: that is the finitely generated statement, equivalent to cost-Betti for all finitely generated groups; this is its restriction to finitely presented groups
  one-relator-group-cost-equals-first-l2-betti-plus-one: that settles the one-relator case; this asks for every finitely presented group
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

**OPEN.** For every infinite finitely presented group `G`, `C(b_G) = 1 + beta_1^(2)(G)`.

This is Gaboriau's cost-Betti question restricted to groups with a finite 2-complex. The finitely presented setting
gives cellular chain complexes with finitely many cell types, so the Morse and relator-circulation methods of the
cycle-tail programme apply with a fixed relator length.

It is one of the two inputs of `fpbs-cycle-tail-compactness-via-length-canonical-covers`. Artifact,
Section 3.
