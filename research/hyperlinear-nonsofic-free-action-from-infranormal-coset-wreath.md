---
rg: 2
id: hyperlinear-nonsofic-free-action-from-infranormal-coset-wreath
kind: route
title: A hyperlinear coset wreath over an intermediate subgroup of the Theorem E pair gives a free hyperlinear nonsofic action
target: hyperlinear-nonsofic-free-action
requires:
  - kt-pair-hyperlinear-floor-below-normal-closure
  - theorem-c-separation-iff-infranormal-coset-wreath
---

For the Theorem E pair `Γ < G`, `kt-pair-hyperlinear-floor-below-normal-closure` supplies
`Δ` with `Γ ≤ Δ`, `⟨⟨Γ⟩⟩ ⊄ Δ` and `W_Δ` hyperlinear. `G` is residually finite, hence sofic,
so Part 3 of `theorem-c-separation-iff-infranormal-coset-wreath` makes the diagonal action
on `({±1},fair)^(G/Δ) × ({±1},fair)^G` free, hyperlinear and not sofic.

This route strictly contains `hyperlinear-nonsofic-free-action-from-kt-wreath` (the case
`Δ = Γ`), and by the same theorem it is the most general route through Kun--Thom Theorem C.
