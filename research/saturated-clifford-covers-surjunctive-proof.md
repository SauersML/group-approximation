---
rg: 2
id: saturated-clifford-covers-surjunctive-proof
kind: route
title: Finite windows of a saturated cover embed with the same coordinates into separated covers
target: profinitely-saturated-clifford-covers-are-surjunctive
requires:
  - clifford-cover-center-separable-iff-graph-is-finite-pullback
  - separated-finite-normal-subgroups-preserve-surjunctivity
  - rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive
  - strict-pairs-transfer-to-table-realizations
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Artifact Section 4, Theorem C.
- **Relevant pairs.** A finite `F` in `E_S` reads adjacency on finitely many relevant site pairs (Section 0).
- **One quotient.** Saturation gives each relevant edge a `K` that separates its endpoints and splits its
  orbit from every relevant non-edge. These properties pass to smaller `K`, so one `K` works for all.
- **The separated cover.** The graph `S'` pulled back from the orbits of the relevant edges' images on
  `K\X` agrees with `S` on the relevant pairs and is a finite pullback. So `E_(S')` is surjunctive, by
  Theorem A, the separated finite-normal theorem, and the lamp-wreath theorem.
- **Embedding and transfer.** The identity on coordinates embeds the multiplication table of `F` into
  `E_(S')`. Corollary 1 of the table-realization theorem then makes `E_S` surjunctive.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including the cross graph
(finite pullback iff `[G : Gammabar]` is finite), the Kun–Thom instance, and Remark 4.1
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 11.3).
