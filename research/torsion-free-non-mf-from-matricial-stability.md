---
rg: 2
id: torsion-free-non-mf-from-matricial-stability
kind: route
title: Stability plus no finite-dimensional representations on the torsion-free group
target: torsion-free-finitely-presented-non-mf
requires: [map-matricial-stability-non-mf, fournier-facio-group-finite-dimensional-shadow, defect-normally-generates-torsion-free-quotient, fournier-facio-group-matricially-stable]
---

## Why sufficient

Let `G` be the Fournier-Facio group: finitely presented, torsion-free,
Kazhdan, infinite.

`defect-normally-generates-torsion-free-quotient` in its strong form gives
`<<pi(S)>> = G`, and then
`fournier-facio-group-finite-dimensional-shadow` clause 3 makes `G`
minimally almost periodic.  With
`fournier-facio-group-matricially-stable`,
`map-matricial-stability-non-mf` applies and `G` is not MF — indeed every
corona representation of `G` is trivial.

This route shares its group-theoretic prerequisite with the primary route
`torsion-free-non-mf-from-normal-kazhdan-defect` and differs only in the
analytic one, where it substitutes a named stability property for the
repository's own normal-Kazhdan obstruction.

## It is no longer an independent route (2026-08-17)

That substitution was the point of keeping this route: if the
small-cancellation prerequisite landed and the normal-Kazhdan obstruction
turned out to have a gap, this route would still reach the root.  **That is
no longer true.**  Its last open prerequisite,
`fournier-facio-group-matricially-stable`, was closed through
[[fournier-facio-asymptotic-representations-trivial]], which proves the
stability of `G` *from* `normal-kazhdan-defect-non-mf` — the very
obstruction this route was held in reserve against.  Both routes into the
root now rest on the same analytic theorem, and a gap in it would take both
down together.

So the graph shows two complete routes into the root and they are **not**
two independent confirmations.  The honest reading: one analytic theorem
(machine-checked, `normal-kazhdan-defect-non-mf-proof`) and one written
group-theoretic argument (`defect-normally-generates-torsion-free-quotient`,
audited but unformalized), reached by two presentations.  A genuinely
independent second route would have to prove matricial stability of `G` by
some other means — a cohomological vanishing argument, say — and no such
proof exists here.

The other cost recorded when this route was written still stands: its
analytic prerequisite is strictly stronger than necessary, since matricial
stability of `G` proves far more than non-MF-ness.  It is now clear *why*
that is so cheap to have — `G` admits no nontrivial finite-dimensional
approximation at all, so its stability is degenerate rather than a repair
phenomenon.
