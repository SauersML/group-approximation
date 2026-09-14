---
rg: 2
id: f-dyadic-inverted-orbit-is-subballistic-on-rare-events
kind: claim
title: The inverted orbit of a random walk on Thompson's F acting on the dyadic rationals is confined to o(n) points on events of only subexponentially small probability
distinct_from:
  f-dyadic-action-is-not-recurrent: that says the mean inverted orbit is ballistic, an established fact; this is the strictly weaker rare-event confinement, which is open and would prove extensive amenability.
  thompson-f-dyadic-action-is-extensively-amenable: that is extensive amenability of the dyadic action; this is its concrete probabilistic form via the inverted orbit, equivalent to it by f-dyadic-ea-iff-inverted-orbit-confinement.
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
---

**OPEN.** Let `μ` be a non-degenerate symmetric finitely supported probability measure on `F` with
generating support, `x_0 ∈ D`, `g_n = h_n⋯h_1` the left random walk, and
`O_n = {x_0, g_1⁻¹x_0, …, g_n⁻¹x_0}` the inverted orbit. Then for every `ε > 0`,

`P(|O_n| < ε n) > e^{−ε n}` for infinitely many `n`.

Equivalently, `E(2^{−|O_n|})` decays subexponentially. By `f-dyadic-ea-iff-inverted-orbit-confinement` this
does not depend on `μ` or `x_0`.

**Status of the two directions.**
- A proof of this claim gives `thompson-f-dyadic-action-is-extensively-amenable`
  (`f-dyadic-ea-from-inverted-orbit-confinement`), hence co-amenability of Jones' subgroup
  (`jones-subgroup-is-co-amenable-in-thompson-f`), answering Aiello–Brothier–Conti Remark 4.7 positively.
- A refutation — a genuine exponential upper bound `E(2^{−|O_n|}) ≤ e^{−cn}`, equivalently exponential decay
  of the switch-walk-switch return probability on `(Z/2)^{(D)} ⋊ F` — proves `F` is not amenable.

**Why it is hard.** The mean is ballistic, `(1/n) E|O_n| → P(T=∞) > 0`
(`f-dyadic-action-is-not-recurrent`), so the confinement is a large-deviation statement: the trajectory
of the inverse walk must, with only subexponentially small probability, stay confined to a vanishing
fraction of the dyadics it would typically escape through. This is a spectral-radius / cogrowth question
for the dyadic lamplighter, of the same order of difficulty as the unsettled cogrowth numerics for `F`
itself (recorded in `research/artifacts/ideas-wildcards-2026-09-14.md`).
