---
rg: 2
id: surjunctive-nonsofic-group-exists
kind: claim
title: Some finitely generated surjunctive group is not sofic
root: true
distinct_from:
  openai-leavitt-unit-nonsofic: that establishes a nonsofic group whose surjunctivity is open; this establishes a nonsofic group that is surjunctive, separating the two properties.
  leavitt-unit-group-nonsurjunctive: that seeks a counterexample to Gottschalk's conjecture on the Leavitt unit group; this exhibits a nonsofic group where the conjecture holds.
artifacts:
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

There is a finitely generated group that is surjunctive and not sofic.
Consequently surjunctivity does not characterize soficity.

*Marked `root` because it answers a top-level question in its own right.*
Gromov and Weiss proved that sofic groups are surjunctive, and Problem 1.1 of
Bowen--Chapman, arXiv:2511.06586, asks whether all surjunctive groups are
sofic. They separate the invariant-random-subgroup analogue: a surjunctive
non-cosofic invariant random subgroup of a free group. They record the group
question as out of reach while no nonsofic group was known.

**Witness.** The Kun--Thom generalized wreath product
`W = (Z/2Z) wr_(G/Gamma) G` for their Theorem E pair.
* Not sofic: Theorem A.
* Surjunctive: `kun-thom-nonsofic-wreaths-are-surjunctive`.
* Finitely generated: `G` is finitely generated and acts transitively on
  `G/Gamma`, so `G` and one lamp generate `W`.

**Second, independent witness.** The group double `G *_Gamma G` of the same
pair.
* Not sofic: `kt-pair-group-double-is-nonsofic`.
* Surjunctive: `kun-thom-group-doubles-are-surjunctive`.

Both witnesses come from `finitary-split-extension-surjunctivity-permanence`.

This does not decide Gottschalk's conjecture, and it does not decide whether
the first nonsofic group, the binary Leavitt unit group, is surjunctive.
