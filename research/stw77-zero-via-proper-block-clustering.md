---
rg: 2
id: stw77-zero-via-proper-block-clustering
kind: route
title: Merge zero-color block clusters and centralize the finite tuple
target: stw77-nucdim-zero-case
requires:
  - stw77-zero-models-admit-proper-block-clustering
  - stw77-near-duplicate-fd-blocks-merge
  - oinfty-map-stability-is-central-isometry-splitting
---

Fix a finite set of contractions and `epsilon>0`, and apply the clustering
claim with `eta<epsilon/4`. The merge lemma gives exact orthogonal isometries
whose commutators with the model tuple are less than `2 eta`. Replacing the
model tuple by the image tuple costs at most another `2 eta`, so every image
commutator is less than `4 eta<epsilon`. Thus the finite-set centralization
defect vanishes. The central-isometry criterion gives O-infinity-stability.
