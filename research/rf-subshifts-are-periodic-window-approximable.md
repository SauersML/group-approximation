---
rg: 2
id: rf-subshifts-are-periodic-window-approximable
kind: claim
title: A perfect subshift is residually finite iff at every window its window SFT has finitely many finite orbits realizing all of its window patterns
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: that is the obstruction for subshifts inside an SFT without finite orbits; this is the two-sided criterion for every perfect subshift, whose sufficiency half builds Kerr–Nowak models from periodic configurations.
  periodic-approximable-subshifts-host-no-fp-simple-group: that defines pointwise periodic approximations with stabilizer avoidance, for a full-group obstruction; this characterizes Kerr–Nowak residual finiteness by window SFTs with covering finite orbits.
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be countable, `A` finite, and `X ⊆ A^Γ` a subshift without isolated
points. For finite `W ⊆ Γ` let `L_W(X) = {x|_W : x ∈ X}` and let
`X_W = {c ∈ A^Γ : (g^(-1)·c)|_W ∈ L_W(X) for all g ∈ Γ}` be the window SFT.

Then `Γ ↷ X` is residually finite in the sense of Kerr–Nowak (Ma, arXiv:2209.00580,
`defn: residually finite action`) iff for every finite `W` there is a finite `Γ`-invariant `O ⊆ X_W`
with `{c|_W : c ∈ O} = L_W(X)`.

**Consequences.**
- Every exact finite model of an RF subshift is a finite union of periodic configurations whose windows are
  windows of `X`, and conversely. A commented-out proposition in Ma's TeX source asserting that every subshift
  over a residually finite group is RF is therefore false (Labbé's shift, `z2-containing-groups-have-non-rf-measure-actions`).
- Used to prove `rf-toeplitz-subshifts-over-residually-finite-groups`.

Route: `rf-subshifts-are-periodic-window-approximable-proof`.
