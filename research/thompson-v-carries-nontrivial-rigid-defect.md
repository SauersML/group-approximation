---
rg: 2
id: thompson-v-carries-nontrivial-rigid-defect
kind: claim
title: Some infranormal Kazhdan pair inside Thompson's V has a nontrivial rigid defect
refuted_by:
  - thompson-v-has-no-rigid-compression-defect
distinct_from:
  hyperlinear-group-carries-nontrivial-rigid-defect: that is the failure branch of the hyperlinear defect criterion, asking for some hyperlinear group with a nontrivial defect; this asks for the defect inside the one group V, as the premise of a nonapproximability proof for V.
  kun-thom-wreath-carries-rigid-defect: that is the established defect of the Kun--Thom wreath over its Theorem E pair; this is the analogous statement for V, which is false.
---

**REFUTED.** There are `Gamma <= G <= V` with `Gamma` and `G` Kazhdan, `Gamma`
infranormal in `G`, and `D_V(G, Gamma) != 1`.

This is the premise the Kazhdan compression mechanism would need in order to
certify `V` nonsofic or nonhyperlinear through `V` itself (routes
`thompson-v-not-sofic-via-rigid-defect` and
`thompson-v-not-hyperlinear-via-rigid-defect`). It is false: every Kazhdan
subgroup of `V` is finite (`thompson-v-has-no-rigid-compression-defect`).

## Attempts

- **Cylinder compressions.** Rigid stabilizers `V_(0*) >= V_(00*)` with a prefix
  compressor carry nontrivial compression defects, but `V_(0*)` is isomorphic
  to `V` and is not Kazhdan. It dies at property (T), and the Haagerup property
  of `V` (Farley) rules out any infinite Kazhdan replacement.
