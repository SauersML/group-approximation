---
rg: 2
id: surface-group-pullbacks-of-measured-z2-actions-are-rf
kind: claim
title: Pulling back a measured Cantor Z^2-system to a closed surface group along a handle retraction always gives a residually finite action
distinct_from:
  z2-containing-groups-have-non-rf-measure-actions: that gives non-RF measured actions of groups containing Z^2; this shows the Z^2 obstruction does not transfer to surface groups along quotient maps, since relator defects are absorbed by a spare handle.
artifacts:
  - research/artifacts/un-class-n-conjecture-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `Γ_g = ⟨a_1,b_1,…,a_g,b_g | [a_1,b_1]⋯[a_g,b_g]⟩` with `g >= 2`, and let
`q : Γ_g -> Z^2` send `a_1 ↦ e_1`, `b_1 ↦ e_2` and all other generators to `0`. For every Cantor `Z^2`-system
`Z` with a full-support invariant probability measure, the action `γ·z = q(γ)·z` of `Γ_g` is residually finite
in the Kerr–Nowak sense.

In particular, Labbé's shift (not RF as a `Z^2`-system) becomes RF when pulled back to `Γ_g`. Residual finiteness
of actions passes to restrictions and factors, but is not reflected along quotient maps of the acting group. So
surface groups are not shown to lie outside `𝔑` through their abelianization.

**Mechanism.**
- Integer flows (Kerr–Nowak) model the handle pair `(a_1,b_1)` by permutations `α, β`.
- Their commutator preserves every coarse atom, because `e_1, e_2` commute.
- Doubling the model makes that defect a square on each atom.
- A square `σ^2` is the commutator `[σ, ρ]`, with `ρ` conjugating `σ^(-1)` to `σ`, so the second handle
  absorbs the defect while acting trivially at the coarse scale.

Route: `surface-group-pullbacks-of-measured-z2-actions-are-rf-proof`.
