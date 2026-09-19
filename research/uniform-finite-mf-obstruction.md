---
rg: 2
id: uniform-finite-mf-obstruction
kind: claim
title: Dimension-independent finite operator-norm obstruction for the literal mark
distinct_from:
  effective-transport-modulus: This claim asserts existence of a finite test and positive threshold by compactness; the other asks for an explicit numerical modulus on the displayed relators.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralUniformObstruction.lean
---

There are a finite subset `F_0` of the literal group and a number `delta > 0`,
independent of matrix dimension, such that every unitary map whose
multiplicative defect is at most `delta` on `F_0` sends the marked word within
operator norm `< 1` of the identity.
