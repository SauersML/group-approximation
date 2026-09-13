---
rg: 2
id: type-fhn-groups-are-of-type-fpn
kind: claim
title: "A group acting properly and cocompactly on an (n-1)-acyclic complex is of type FP_n"
distinct_from:
  every-type-fpn-group-is-of-type-fhn: that claim is the open implication FP_n implies FH_n; this is the elementary converse FH_n implies FP_n
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part1.md
---

If a group `G` acts cellularly on an `(n−1)`-acyclic CW complex with finite
cell stabilizers and finitely many orbits of cells, then `G` is of type
`FP_n` over `ℤ`.

This is the known direction of Zaremsky Problem 1.4. For the free reading,
Leary (arXiv:1512.06609, in the section recalling finiteness properties)
records `F_n ⇒ FH_n(R) ⇒ FL_n(R) ⇒ FP_n(R)`.

Proof (Theorem A of the artifact): replace the action by a free one
(`proper-and-free-type-fhn-coincide`) and truncate to the `n`-skeleton. The
cellular chains then form an exact sequence
`C_n → ⋯ → C_0 → ℤ → 0` of finitely generated free `ℤG`-modules.
