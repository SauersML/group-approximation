---
rg: 2
id: retract-images-of-full-shifts-are-not-disjoint-unions
kind: claim
title: Over an infinite group no retract image of a full shift is a disjoint union of two nonempty subshifts
distinct_from:
  retract-images-of-full-shifts-have-infinite-descending-chains: that node concerns nested retract images; this one says a single retract image never splits into two subshifts, so additive Grothendieck classes cannot record a drop.
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
---

Let `G` be infinite, `A` finite, and `X = f(A^G)` the image of an idempotent cellular automaton `f`.
Then `X` is not a disjoint union `X_1 ⊔ X_2` of two nonempty subshifts.

Consequences for sizes built from subshift classes:
- In a Grothendieck group of subshifts modulo conjugacy with `[X ⊔ Y] = [X] + [Y]`, retract images are
  indecomposable, so no relation writes `[A^G]` as the class of a proper retract plus a remainder.
- Every conjugacy-invariant class, additive or multiplicative, is equal at `A^G` and at `tau(A^G)`
  for a strict `tau`, because `tau` is a conjugacy onto its image.
- So Grothendieck-type invariants of subshifts cannot supply the drop on proper retracts asked for by
  `surjunctivity-iff-automaton-monoid-directly-finite`.

Proof: artifact Section 4, route `retract-images-not-disjoint-unions-proof`.
