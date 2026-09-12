---
rg: 2
id: fg-simple-subgroups-of-local-embedding-free-closure-are-sofic
kind: claim
title: Without local embeddings, the surjunctivity permanence closure of sofic groups has only sofic finitely generated simple subgroups
distinct_from:
  gottschalk-counterexamples-lie-outside-the-permanence-closure: that keeps local embeddings (O3) and excludes finitely presented simple nonsofic groups; this drops O3 and excludes every finitely generated simple nonsofic group, with no finite presentation.
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that excludes finitely presented simple nonsofic groups with property FA under a different operation list; this concerns all finitely generated simple subgroups of the O3-free surjunctivity closure.
artifacts:
  - research/artifacts/fg-simple-groups-and-the-permanence-closure-2026-09-12.md
---

Let `S*_0` be the smallest class of groups containing every sofic group and closed
under the operations O1, O2, O4, O5, O6 and O7 of
`gottschalk-counterexamples-lie-outside-the-permanence-closure`:

- subgroups;
- groups whose finitely generated subgroups all lie in the class;
- split extensions with a finitary site structure;
- graphs of groups with a homomorphism into the class injective on vertex groups;
- graph wreath products with LEF lamps;
- split extensions with finitely generated residually finite kernel.

Every finitely generated simple subgroup of a group in `S*_0` is sofic.

**Consequence.** Suppose some infinite finitely generated simple nonsofic group `Q`
is surjunctive by the landed permanence methods, meaning `Q` lies in `S*`. Then `Q`
enters `S*` through local embeddings (O3), and `Q` is not finitely presented.
Conversely, any such `Q` that is locally embeddable into `S*` is surjunctive. This
is the only door to a positive case on a simple nonsofic host;
`permanence-closure-contains-fg-simple-nonsofic-group` asks whether it opens.

Proof: Section 1 of the artifact, route
`fg-simple-subgroups-local-embedding-free-closure-proof`.
