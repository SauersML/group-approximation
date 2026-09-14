---
rg: 2
id: f-dyadic-ea-from-inverted-orbit-confinement
kind: route
title: Rare-event confinement of the inverted orbit yields extensive amenability of the dyadic action through the inverted-orbit equivalence
target: thompson-f-dyadic-action-is-extensively-amenable
requires:
  - f-dyadic-inverted-orbit-is-subballistic-on-rare-events
  - f-dyadic-ea-iff-inverted-orbit-confinement
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
---

Modus ponens. `f-dyadic-ea-iff-inverted-orbit-confinement` establishes that extensive amenability of
`F ↷ D` is equivalent to condition (ii), the rare-event confinement of the inverted orbit. That condition is
the claim `f-dyadic-inverted-orbit-is-subballistic-on-rare-events` (OPEN). Its truth therefore gives
`thompson-f-dyadic-action-is-extensively-amenable`.

This is a genuine reduction rather than a restatement: the target is a mean/invariant-mean statement on
`P_f(D)`, while the prerequisite is an intrinsic large-deviation bound on a random walk on `F`, checkable in
principle by spectral-radius or cogrowth estimates for the dyadic lamplighter `(Z/2)^{(D)} ⋊ F`, and known
to be strictly weaker than the failed recurrence condition (`f-dyadic-action-is-not-recurrent`).
