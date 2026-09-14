---
rg: 2
id: free-rf-actions-force-residually-finite-groups
kind: claim
title: A free residually finite action forces the acting group to be residually finite, so no free subshift over a non-RF group has periodic window models
distinct_from:
  rf-subshifts-are-periodic-window-approximable: that characterizes RF subshifts by periodic window models; this shows such models force the acting group itself to be residually finite when the action is free.
  sfts-without-finite-orbits-are-not-residually-finite-actions: that obstructs residual finiteness through the subshift (an SFT without finite orbits); this obstructs it through the acting group, for every free action.
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; route `free-rf-actions-force-residually-finite-groups-proof`, artifact §1).**

Let a countable group `Γ` act continuously and freely on a compact metric space `X`. Suppose the action is residually finite in the sense of Kerr–Nowak (Ma, arXiv:2209.00580, `defn: residually finite action`). Then `Γ` is residually finite.

**Consequences.**
1. Over a finitely generated group that is not residually finite, no free subshift is window-periodic (`rf-subshifts-are-periodic-window-approximable`). Examples: `BS(2,3)`, Higman's group, Thom's finitely generated Kazhdan LEF group that is not RF, and the derived topological full group of a minimal `Z`-subshift.
2. The RF route to LEF Kazhdan simple groups (`residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`) reaches exactly the residually finite acting groups.
3. For LEF acting groups that are not RF, only partial models can work: `window-lef-subshifts-give-matricial-crossed-products`.

**Model test.** `Γ = Z` acting on an infinite minimal subshift: the action is free and RF, and `Z` is RF. The trivial group acting on a Cantor set is not free, and the lemma says nothing about it.
