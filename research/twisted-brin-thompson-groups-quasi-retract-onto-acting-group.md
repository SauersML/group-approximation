---
rg: 2
id: twisted-brin-thompson-groups-quasi-retract-onto-acting-group
kind: claim
title: A finitely generated twisted Brin--Thompson group SV_G quasi-retracts onto G, so G is undistorted in SV_G
distinct_from:
  full-group-label-length-bounds-distortion: that is a lane-proved label-length lemma whose twisted form gives undistortion of G in SV_G; this imports the Belk--Zaremsky theorem, which gives more (a coarse Lipschitz retraction SV_G -> G).
  twisted-brin-thompson-finite-presentation-criterion: that is the criterion for SV_G to be finitely presented; this is the geometry of the canonical embedding of G once SV_G is finitely generated.
  twisted-brin-thompson-groups-embed-along-equivariant-inclusions: that embeds one twisted Brin--Thompson group in another along an equivariant inclusion of actions; this compares G with its own SV_G metrically.
---

**ESTABLISHED (literature import).**

> **Theorem 2 (Belk--Zaremsky, arXiv:2001.04579, introduction, `thm:quasi-retracts`).** Suppose
> G and SV_G are finitely generated. Then there exists a coarse Lipschitz map
> ρ: SV_G → G such that ρ ∘ ι_∅ is the identity. In particular, the group SV_G
> quasi-retracts onto G, and ι_∅ is a quasi-isometric embedding of G into SV_G.

Here `G` acts faithfully on a set `S`, and `ι_∅` is the canonical embedding of `G` into `SV_G`, by
coordinate permutations of `C^S`. `SV_G` is finitely generated exactly when `G` is finitely
generated and has finitely many orbits on `S` (their `thm:FinitelyGeneratedTheorem`).

**Use.** Every group that is undistorted in the acting group `G` of a finitely generated `SV_G` is
undistorted in `SV_G`. When `SV_G` is finitely presented and simple (for example through
`twisted-brin-thompson-finite-presentation-criterion`), that gives a quasi-isometric embedding into a
finitely presented simple group. So for the "(quasi-isometrically?)" refinement of the permutational
Boone--Higman embeddings, the only step with content is the embedding of the group into the acting group.

Nothing is reproved here, and there is no Lean counterpart.
