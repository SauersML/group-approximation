---
rg: 2
id: fp-simple-amenable-folner-growth-via-boone-higman
kind: route
title: Embed the decidable diagonal product that beats U into a finitely presented simple group
target: fp-simple-amenable-subgroups-beat-every-recursive-folner-bound
requires:
  - boone-higman-conjecture
  - decidable-amenable-groups-have-no-recursive-folner-bound
---

Fix a recursive non-decreasing `U`.

- `decidable-amenable-groups-have-no-recursive-folner-bound` gives a finitely
  generated elementary amenable group `Δ_U` with solvable word problem and
  `F_(Δ_U) ⋠ U`.
- `boone-higman-conjecture` embeds `Δ_U` in a finitely presented simple group
  `S`.
- `Δ_U` is then a finitely generated amenable subgroup of `S` with `F ⋠ U`.
  `∎`

**Contrapositive.** A recursive `U` such that every finitely generated
amenable subgroup of every finitely presented simple group has `F ≼ U` would
refute Boone--Higman. See `folner-separators-of-boone-higman`, item 5.

**Remaining input.** Only the embedding of the specific groups `Δ_U`. See
Attempt 3 of the target for what is known about them.
