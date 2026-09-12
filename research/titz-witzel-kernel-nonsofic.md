---
rg: 2
id: titz-witzel-kernel-nonsofic
kind: claim
title: The smallest Titz--Witzel simple Kazhdan kernel is not sofic
invalidates:
  - torsion-free-sofic-exact-mf-radical-via-titz-witzel
distinct_from:
  titz-witzel-kernel-sofic: this is its negation.
  openai-leavitt-unit-nonsofic: that is the nonsofic Leavitt unit group from the one-sided compression criterion; this would be a nonsofic torsion-free simple Kazhdan CAT(0) lattice, where no compression pair is known.
artifacts:
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
refuted_by:
  - titz-witzel-kernel-sofic
---

**OPEN.**  This is the negation of `titz-witzel-kernel-sofic`.  If
established it kills the Titz--Witzel route to the torsion-free exact-radical
goal.  It would also give a nonsofic CAT(0) group with property `(T)` by a
mechanism different from the compression criterion behind every nonsofic
group known today.

## Attempts

* **Stability repair.**  A dimension-independent inequality bounding the
  distance to a genuine finite action by the density of bad radius-five balls
  would finish this through `sofic-stable-implies-residually-finite`.
  Property `(T)`, ball rigidity, expander decomposition and Chapman--Lubotzky
  do not supply it (audit artifact).
* **Radu sublattice.**  Nonsoficity of Radu's non-residually-finite BMW
  lattice suffices, since that lattice embeds in `K` up to index four
  (`titz-witzel-kernel-nonsofic-from-radu-lattice`).  There, Lemma 3.5 of
  Titz Mite--Witzel is fully quantitative
  (`radu-mark-is-controlled-by-one-commutator`).  The only exact-quotient
  input left to make robust is Radu's Proposition 5.4, the collapse of one
  commutator.
