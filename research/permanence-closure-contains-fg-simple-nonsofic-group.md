---
rg: 2
id: permanence-closure-contains-fg-simple-nonsofic-group
kind: claim
title: Some infinite finitely generated simple nonsofic group lies in the surjunctivity permanence closure
root: true
distinct_from:
  finitely-generated-simple-groups-are-surjunctive: that is the universal reduction of Gottschalk's conjecture; this asks for one simple nonsofic group that the landed permanence methods already make surjunctive.
  gottschalk-counterexamples-lie-outside-the-permanence-closure: that excludes finitely presented simple nonsofic groups from S*; this asks whether any finitely generated, necessarily infinitely presented, simple nonsofic group lies in S*.
  fg-simple-subgroups-of-local-embedding-free-closure-are-sofic: that proves the O3-free closure contains no such group; this asks whether local embeddings supply one.
artifacts:
  - research/artifacts/fg-simple-groups-and-the-permanence-closure-2026-09-12.md
---

**OPEN.** There is an infinite, finitely generated, simple, nonsofic group `Q` in the
closure `S*` of `gottschalk-counterexamples-lie-outside-the-permanence-closure`.

**Why it matters.**
- Every group of `S*` is surjunctive, so `Q` would be the first simple nonsofic group
  known to be surjunctive: a positive case of Gottschalk's conjecture on a simple
  nonsofic host, in the class to which the conjecture reduces.
- By `fg-simple-subgroups-of-local-embedding-free-closure-are-sofic`, `Q` must enter
  through local embeddings and cannot be finitely presented. The target is therefore
  an infinitely presented simple nonsofic group every finite ball of which embeds as a
  partial multiplication table into a group of `S*`.

*Marked `root` because it asks a top-level question in its own right, like
`surjunctive-nonsofic-group-exists`.*

## Attempts

- **Unions, folds and extensions.** They are dead by the O3-free theorem. A simple
  amalgam or HNN extension folding faithfully on vertex groups into a surjunctive `G`
  embeds into `G`, since the fold kernel is free. A directed union containing a
  finitely generated simple `Q` already contains it at a finite stage.
- **Simple subgroups of known witnesses.** Kun–Thom wreaths, doubles and graph wreaths
  have sofic kernels over residually finite or sofic bases, so every finitely generated
  simple subgroup is sofic. Nothing to extract.
- **Marked limits of wreaths with growing finite simple lamps.** `Alt(k_n) wr_(G/Gamma) G`
  lies in `S*` and contains the Kun–Thom wreath. As `k_n` grows, the limit is a wreath
  with LEF lamps: surjunctive and nonsofic, but the lamp subgroup stays normal. A
  simple limit needs base generators to become short products of lamp commutators in
  the limit. No design is known yet.
- **Next candidates (not tried).** Topological full groups of the Kun–Thom generalized
  Bernoulli action, whose commutator subgroups are simple under minimality, and small
  cancellation embeddings of a Kun–Thom wreath into infinitely presented simple groups.
  For each, test local embeddability of balls into permutational wreath products over
  the Kun–Thom base.
