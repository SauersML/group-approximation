---
rg: 2
id: tracial-npa-cannot-separate-canonical-trace
kind: claim
title: A standard tracial NPA dual cannot be a matrix-only separator negative on the canonical trace
distinct_from:
  global-tracial-positivity-cannot-separate-group-trace: that rules out any globally tracial positivity proof; this identifies the standard tracial NPA dual cone as one such proof system and fixes the computational consequence.
  atlas-radius-nine-trace-separator: that asks for an inequality valid only in matrices; this explains why a dimension-blind tracial moment hierarchy cannot extract it.
---

Let `Gamma=<S|R>` and let `tau_Gamma` be its canonical group trace.  Every
finite level of the standard tracial NPA/Lasserre hierarchy imposes only
positive semidefiniteness of a truncated tracial moment matrix together with
the group relations.  The truncated moments of `tau_Gamma` are feasible at
every level.

Consequently every sound dual certificate from that hierarchy is nonnegative
on `tau_Gamma`.  It cannot certify a trace polynomial `P` which is nonnegative
on all finite matrices (up to relator penalties) but satisfies
`tau_Gamma(P)<0`.

Thus the radius-nine campaign must use a genuinely matricial hierarchy or a
dimension-sensitive invariant-theory proof system.  Calling a standard
tracial NPA solver and interpreting its dual as the desired separator is
unsound.
