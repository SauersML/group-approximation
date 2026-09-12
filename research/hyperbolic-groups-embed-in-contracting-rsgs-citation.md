---
rg: 2
id: hyperbolic-groups-embed-in-contracting-rsgs-citation
kind: route
title: Import Theorem 1.4 of Belk--Bleak--Matucci--Zaremsky, that every hyperbolic group embeds in a full contracting rational similarity group
target: hyperbolic-groups-embed-in-contracting-rsgs
requires: []
artifacts:
  - research/artifacts/bh-rational-similarity-hosts-2026-09-12.md
---

Citation import. Read on 2026-09-12 from the arXiv TeX source of
J. Belk, C. Bleak, F. Matucci, M. C. B. Zaremsky, *Hyperbolic groups satisfy the
Boone--Higman conjecture*, arXiv:2309.06224v3 (file
`hyperbolic_boone_higman.tex`, fetched and grepped on MSI):

- `thrm:hyp_to_contracting`, verbatim: "Every hyperbolic group embeds into a full,
  contracting~RSG." The introduction restates it as `thrm:hyp_embed`: "Every
  hyperbolic group embeds in a full, contracting RSG."
- The proof (TeX lines 1741--1742) first passes to `G * Z`. It then uses the tree
  of atoms of the horofunction boundary, the rationality theorem of
  Belk--Bleak--Matucci, `prop:hyp_similarities` (the image is an RSG),
  `thrm:contracting` (finite nucleus) and `thrm:RSGCharacterization` (the full
  group is a full, contracting RSG).

The definitions of RSG, local action, nucleus and contracting are quoted in the
linked artifact. Nothing here is reproved.
