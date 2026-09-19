---
rg: 2
id: kun-thom-single-compressor-sofic-joint-nonsofic-proof
kind: route
title: Apply the monomial HNN theorem one compressor at a time and Kun--Thom to the full action
target: kun-thom-single-compressor-sofic-joint-nonsofic
requires:
  - monomial-ascending-hnn-coset-action-sofic
  - coordinate-action-not-sofic
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Each positive elementary compressor `I+E_ij` is an injective nonnegative
monomial matrix with nonzero determinant, so
`monomial-ascending-hnn-coset-action-sofic` applies to the subgroup generated
by the base and that single stable letter.  This proves every one-compressor
restriction sofic.

The prerequisite `coordinate-action-not-sofic` is the already source-verified
Kun--Thom conclusion for the full ambient group.  Putting the two statements
together gives the claimed localization of the obstruction.
