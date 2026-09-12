---
rg: 2
id: surjunctive-nonsofic-group-via-faithful-vertex-fold
kind: route
title: Apply the faithful vertex fold theorem to a nonsofic Kun--Thom double
target: surjunctive-nonsofic-group-exists
requires:
  - graph-folds-over-surjunctive-groups-are-surjunctive
  - kt-pair-group-double-is-nonsofic
  - kun-thom-nonsofic-wreath
  - residually-finite-groups-are-surjunctive
artifacts:
  - research/artifacts/surjunctivity-graph-folds-2026-09-11.md
---

Take the explicit Theorem E pair `Gamma<G` recorded in
`kun-thom-nonsofic-wreath`. Its actor `G` is residually finite, hence
surjunctive. For the double `D=G *_Gamma G`, the fold `D->G` is the
identity on both vertex groups. The graph-fold theorem therefore makes
`D` surjunctive. The strengthened Kun--Thom Theorem A gives nonsoficity.

Both copies of `G` are finitely generated, so their union finitely
generates `D`. Thus `D` is a finitely generated surjunctive nonsofic
group, proving the existing separation target by a group double.

The double case was already proved in the preexisting finitary artifact;
this route records it as a consequence of the stronger graph-of-groups
theorem, with explicit graph dependencies. It does not claim a new
priority for the witness or for the inherited peeling proof.

Freshness check 2026-09-11: the
[current arXiv record](https://arxiv.org/abs/2608.06222) remains version 3,
20 August 2026. Its
[Theorems A and E](https://arxiv.org/html/2608.06222v3#Thmtheorem1)
give respectively the double conclusion and the residually finite
Kazhdan example. The imported nonsoficity has the source's preprint
status; no independent proof of that input is claimed here.
