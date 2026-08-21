---
rg: 2
id: nonhyperlinear-from-algebraic-compact-action-envelope
kind: route
title: Compile an algebraic envelope of the non-CE relation into a discrete non-hyperlinear group
target: non-hyperlinear-group
requires:
  - algebraic-compact-action-envelope-for-non-ce-relation
  - algebraic-compact-action-group-factor-compiler
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
---

Apply `algebraic-compact-action-group-factor-compiler` to the embedding
`(ACAE1)`.  It identifies the ambient crossed product with
`L(K-hat rtimes Lambda)`, so Connes embeddability of that canonical group
factor would force the embedded relation factor to be Connes embeddable.
Thus `K-hat rtimes Lambda` is non-hyperlinear.  Under the effective
finite-generation hypotheses in the envelope claim, Higman's embedding
theorem supplies a finitely presented non-hyperlinear overgroup.

