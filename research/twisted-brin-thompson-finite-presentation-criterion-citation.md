---
rg: 2
id: twisted-brin-thompson-finite-presentation-criterion-citation
kind: route
title: Import Zaremsky's criterion, cross-checked against Fournier-Facio-Wu-Zaremsky Theorem B
target: twisted-brin-thompson-finite-presentation-criterion
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Citation import, from two independent statements read from source
2026-08-17: Zaremsky arXiv:2405.18354 (the criterion verbatim, from the
abstract) and Fournier-Facio--Wu--Zaremsky arXiv:2603.24687v2 Definition 1.3
together with Theorem B (the same conditions in `F_n` language, specialized
at `n = 2`).  Quotations in
`research/artifacts/boone-higman-audit-2026-08-17.md` §A.1.

Not reproved here and no Lean counterpart exists.

## Why two sources rather than one

Because the attempt that brought this region in cited a third statement that
does not exist (§A.3 of the audit).  Having the criterion in two independently
read forms — an if-and-only-if in one paper's abstract, and a
finiteness-properties theorem plus definition in another's body — means a
misreading of either one would have to be a misreading of both to survive.
They agree.

The two forms differ in one harmless detail: Zaremsky counts orbits of
two-element **subsets**, FFWZ counts orbits of the diagonal action on ordered
pairs.  For the transitive coset actions used in this region the two are
finite together, so no node distinguishes them.

## Trust surface

Simplicity of `SV_G` under faithfulness is the older part of the theory and
was not re-read this session; only finite presentability was.  Both halves
are consumed by `boone-higman-via-finite-bi-index-envelope`, so a failure in
either would take that route with it.
