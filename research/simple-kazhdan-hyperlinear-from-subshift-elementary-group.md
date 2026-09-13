---
rg: 2
id: simple-kazhdan-hyperlinear-from-subshift-elementary-group
kind: route
title: A simple Kazhdan LEF group is sofic, hence hyperlinear, and so answers Pestov 9.1
target: infinite-simple-kazhdan-hyperlinear-group
requires: [simple-kazhdan-lef-group-from-minimal-subshift]
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
---

Assume `simple-kazhdan-lef-group-from-minimal-subshift`. That claim is OPEN and under independent
review, so this route does not fire before the review lands.

`S = EL_3(LC(X,F_q) ⋊ Z)/Z` is infinite, simple and Kazhdan, and it is LEF. A LEF group is sofic.
Given a finite `F ⊆ S`, an injective partial homomorphism `F·F -> Q` into a finite group, composed
with the left regular action of `Q` on itself, gives a permutation model that is exact on `F` and
separates `F` with Hamming distance `1`. A sofic group is hyperlinear, since permutation matrices
are unitaries whose normalized Hilbert--Schmidt distance is controlled by the Hamming distance. So
`S` witnesses the target in its hyperlinear form, and also in the stronger sofic form of Pestov's
question.

Independent cross-check: `S` is LEF, hence operator MF (`lef-implies-operator-mf`), and the
kernel-checked `kazhdan-mf-hyperlinear-fragment` makes every simple Kazhdan MF group hyperlinear.
