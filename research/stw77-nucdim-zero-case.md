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
- `stw77-fd-commutant-splitting-iff-proper-supports` identifies the exact
  obstruction inside each one-sided finite-dimensional model: its relative
  commutant contains the required orthogonal isometries if and only if every
  minimal block support is properly infinite.  Hence
  `stw77-proper-support-models-force-oinfty-stability` closes the zero-case
  whenever the models can be selected with no finite support block.  This
  assumption is strictly weaker than returning their projections to the
  projectionless range, but is not yet forced by nuclear dimension zero.
- As a consequence, `stw77-zero-maps-into-projectionwise-proper-targets`
  proves the entire zero-color assertion whenever every nonzero projection
  of the target is properly infinite.  It does not even require proper
  infiniteness of all nonzero image positive elements.
- Conversely, `stw77-zero-counterexamples-trap-nonproper-model-corners`
  shows that any remaining counterexample has one finite image packet which
  forces a nonproper minimal block support in every sufficiently accurate
  unital finite-dimensional model.  The obstruction is therefore uniform,
  not an artefact of choosing a bad approximation.
- The `B(H)`-target theorem supplies a different positive mechanism:
  essential representation absorption merges two whole copies of the range
  and never asks finite-dimensional support projections to return.
- One-sided approximation alone is insufficient because generated models can
  contain finite blocks carried by representations which become pointwise
  indistinguishable.  A viable proof must centralize the finite tuple while
  merging or ignoring these blocks; it cannot require their supports to
  become properly infinite or return to a projectionless image.
