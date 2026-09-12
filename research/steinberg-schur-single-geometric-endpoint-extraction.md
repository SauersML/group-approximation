---
rg: 2
id: steinberg-schur-single-geometric-endpoint-extraction
kind: route
title: Extract the endpoint derivative with one geometric row weighting
target: steinberg-rank-one-schur-pivot-is-invertible
requires:
  - steinberg-schur-corrected-endpoint-reduction
---

**INVALIDATED ONE-WEIGHT EXTRACTION.**  The proposed proof weights row `j`
of the corrected endpoint matrix by `t^(j-1)` and seeks a nonzero multiple
of `c_v=(-1)^(v-1)v`.

`steinberg-schur-geometric-row-transform` computes that row combination
exactly.  For every `p>=11`, it retains a nonzero quadratic polynomial term
in addition to at most four exponential families, so no single weight can
equal the endpoint row.  A successful global proof must combine at least two
weights and cancel all four Möbius-push exponential families, or use a
different endpoint argument.
