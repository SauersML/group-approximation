---
rg: 2
id: group-ring-lef-iff-group-lef-iff-elementary-group-lef
kind: claim
title: F_q[Γ] is a LEF ring iff Γ is LEF iff EL_n(F_q[Γ]) is LEF; for amenable non-LEF Γ the ring is stably finite with a faithful rank model while its Kazhdan elementary groups are not LEF
artifacts:
  - research/artifacts/un-calibration-table-2026-09-13-part1.md
  - research/artifacts/un-calibration-table-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed)** by `group-ring-lef-iff-group-lef-iff-elementary-group-lef-proof`.

**Statement.** Let `q` be a prime power, `Γ` a countable group and `n >= 2`.
1. The following are equivalent:
   - (i) `F_q[Γ]` embeds unitally in an algebraic ultraproduct of matrix rings over finite fields (a LEF ring);
   - (ii) `Γ` is LEF;
   - (iii) `EL_n(F_q[Γ])` is LEF.
2. If `Γ` is amenable, `F_q[Γ]` has a faithful Sylvester matrix rank function from Følner truncation. So it is stably finite, and
   `EL_n(F_q[Γ])` is `F_q`-linear sofic.
3. Let `Γ` be finitely generated, amenable and not LEF, and `n >= 3`. Then `EL_n(F_q[Γ])` has property (T) (EJZ), is `F_q`-linear sofic,
   and is not LEF, while `F_q[Γ]` is stably finite with a faithful rank model.

**UN calibration (U2, U3).** Stable finiteness and faithful rank-metric models do not make elementary groups LEF: exact (LEF-ring)
models are needed. Finitely presented amenable groups that are not residually finite are examples of item 3, since finitely presented
and LEF imply residually finite (as recorded in `labbe-shift-derived-full-group-is-lef`). The existence of such groups is recalled, not
quoted here. Rows 14–15 of the calibration table.
