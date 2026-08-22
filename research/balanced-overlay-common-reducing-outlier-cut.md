---
rg: 2
id: balanced-overlay-common-reducing-outlier-cut
kind: claim
title: The balanced overlay admits one common reducing cut for all high square-function outliers
distinct_from:
  raw-relator-square-function-is-automatically-covariant: that constructs and estimates the positive error operator for any residual family; this applies spectral coarea and rounds the tuple to make its high cut literally reducing
  complete-pair-overlay-uniform-hs-basin-capture: that must also correct the diffuse low-square-function complement; this removes only the sparse high-energy obstruction
---

For every fixed `0<a<b<C`, a shared-reflection tuple of balanced energy `E`
has a projection `p` and reflections `V_1,...,V_L` such that

```text
 tau(p)<=O(E/a),
 [p,V_i]=0,
 avg_i ||Q_i-V_i||_2^2 <= O(sqrt(E)/(b-a)),              (BRC1)
```

and `p` is a threshold projection of the raw balanced residual square function.
Hence its complement has square-function operator bound `qHq<=bq` before
the block-diagonal rounding.  The outlier trace and the average cost both
vanish with `E`, uniformly in length and dimension.

This is an outlier quarantine, not the full basin theorem: changing the
reflections to make `p` reducing perturbs the compressed residuals, and an
operator-row/square-function Newton theorem is still needed on `q`.
