---
rg: 2
id: titz-witzel-kernel-nonsofic-from-unrestricted-cover-equivalence
kind: route
title: The cover equivalence without a link hypothesis, applied to the Titz--Witzel complex with a square wedged on, forces the simple kernel to be nonsofic
target: titz-witzel-kernel-nonsofic
requires:
  - sparse-fully-branched-covers-iff-sofic-simple-residual
  - finite-branched-covers-force-connected-vertex-links
---

This route records a calibration, not a plan: it shows that
`sparse-fully-branched-covers-iff-sofic-simple-residual`, in the generality
in which it is stated, is at least as strong as
`titz-witzel-kernel-nonsofic`.  So nobody should expect to establish it
without deciding that question; the usable form is
`sparse-fully-branched-covers-iff-sofic-with-connected-links`.

1. Let `Y'` be `Y_1^2` with a unit square wedged on at a vertex.  By Part 3
   of `finite-branched-covers-force-connected-vertex-links`, `Y'` is a finite
   connected piecewise Euclidean 2-complex with finitely many shapes, locally
   CAT(0), with `pi_1(Y') = pi_1(Y_1^2)` and the same infinite simple
   finite-index subgroup `K`.  So `Y'` satisfies the Setting of
   `sparse-fully-branched-covers-iff-sofic-simple-residual`, which puts no
   condition on the links of the base.
2. By the same Part 3, `Y'` has no finite branched cover.  So item 3 of that
   claim fails for `Y'` (it needs covers `X_n` carrying a positive fraction
   `c` of their sheets in branched components, so `X_n` is nonempty).
3. By its 1 <=> 3, item 1 fails: `K` is not sofic.  This `K` is the finite
   residual of `pi_1(Y_1^2)`, so `titz-witzel-kernel-nonsofic` holds.
