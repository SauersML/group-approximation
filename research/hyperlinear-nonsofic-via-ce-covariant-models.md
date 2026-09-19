---
rg: 2
id: hyperlinear-nonsofic-via-ce-covariant-models
kind: route
title: CE covariant models for actions of the Kun--Thom group make its binary coset wreath a hyperlinear nonsofic group
target: hyperlinear-nonsofic-group
requires:
  - hyperlinear-group-actions-have-ce-covariant-models
  - free-action-covariant-models-contain-the-crossed-product
  - kun-thom-nonsofic-wreath
---

1. Let `Gamma < G` be the Theorem E pair of `kun-thom-nonsofic-wreath`. `G` is residually finite,
   hence hyperlinear.
2. Q1 = `hyperlinear-group-actions-have-ce-covariant-models`, applied to the free Kun--Thom action
   `G ↷ {0,1}^(G/Gamma) × {0,1}^G`, gives a covariant model in a CE algebra.
3. By item 1 of `free-action-covariant-models-contain-the-crossed-product`, that model contains the
   crossed product. By item 2 and Step 5 of its proof, the crossed product contains
   `L^infinity({0,1}^(G/Gamma)) ⋊ G ≅ L(W)`, where `W = (Z/2) wr_(G/Gamma) G`.
4. So `W` is hyperlinear. By Theorem A, `W` is not sofic.

**Scope.** Only Q1 for the one group `G` and the one free action above is used. That instance of
Q1 is equivalent to CE of the crossed product
`L^infinity({0,1}^(G/Gamma) × {0,1}^G) ⋊ G = L((Z/2) wr_(G/Gamma ⊔ G) G)`. This is at least as
strong as hyperlinearity of `W`, which is equivalent to hyperlinearity of the Kun--Thom double by
`kt-wreath-hyperlinear-iff-double-hyperlinear`. So the route is a reframing that places Q1 above a
known hard target. It is not a reduction of that target to something weaker.

**What it changes.**
- `hyperlinear-group-actions-have-ce-covariant-models` now serves `hyperlinear-nonsofic-group`.
- Together with `nonhyperlinear-via-full-subgroup-covariant-models` it shows that the covariant-model
  route to `non-hyperlinear-group` presupposes a positive answer to the Kun--Thom wreath question.
- Every route into `non-hyperlinear-group` that proves `W` or the Kun--Thom double nonhyperlinear
  refutes Q1.
