---
rg: 2
id: type-fp2-groups-are-of-type-fh2-proof
kind: route
title: "FP_2 implies FH_2 by attaching finitely many orbits of 2-cells to a Cayley graph"
target: type-fp2-groups-are-of-type-fh2
requires: []
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part1.md
---

Complete proof in Theorem B of
`research/artifacts/zp-fpn-fhn-2026-09-13-part1.md`, §4.

- `n = 0`: the discrete set `G`.
- `n = 1`: a finitely generated augmentation ideal gives finite generation,
  and the Cayley graph works.
- `n = 2`: by the generalized Schanuel lemma (Lemma S, §1),
  `Z_1 = H_1(Γ)` of a Cayley graph `Γ` is finitely generated. Hurewicz
  `π_1(Γ) → H_1(Γ)` is onto, so finitely many orbits of 2-cells along
  closed loops kill `H_1`.

Unreviewed.
