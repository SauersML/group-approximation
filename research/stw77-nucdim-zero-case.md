---
rg: 2
id: stw77-nucdim-zero-case
kind: claim
title: STW LXXVII has a positive answer for nuclear-dimension-zero maps
root: true
---

Every map satisfying the hypotheses of STW LXXVII and having nuclear
dimension zero is O-infinity-stable.

## Attempts

- Nuclear dimension zero yields one-sided local finite-dimensional models on
  the codomain side, but the proposed projection-return upgrade is false:
  `stw77-z-o2-map-defeats-projection-return` supplies a zero-dimensional
  `Z->O_2` instance with nontrivial projectionless range.  The route
  `stw77-zero-case-via-projection-return` is therefore invalidated.
- The AF-range theorem proves the case in which the local models can be
  chosen internally and coherently.
- One-sided approximation alone is insufficient because generated models can
  contain finite blocks carried by representations which become pointwise
  indistinguishable.  A viable proof must centralize the finite tuple while
  merging or ignoring these blocks; it cannot require their supports to
  become properly infinite or return to a projectionless image.
