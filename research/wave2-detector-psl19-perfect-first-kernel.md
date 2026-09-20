---
rg: 2
id: wave2-detector-psl19-perfect-first-kernel
kind: claim
title: An explicit hyperbolic PSL2(19) triangle has a perfect torsion-free first kernel
distinct_from:
  hyperbolic-triangle-colimit-with-persistent-edge-twist: that is an unresolved all-finite-covers persistence target; this pins one triangle by explicit matrices and computes its first kernel's entire integral abelianization
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-detectors-2026-09-20.md
  - experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel.py
  - experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel_result.json
  - experiments/hrf-wave2-detectors-2026-09-20/psl19_residual.json
---

Let `Q=PSL_2(F_19)` and take the classes of matrices

```
x_12 = [[2,11],[16,3]],
x_13 = [[5,11],[4,9]],
x_23 = [[6,15],[12,8]].
```

Every `x_e` has order five and every pair generates `Q`. Form the triangle
with vertex groups three copies of `Q`, edge groups `C_5` identified
through these elements, and trivial face group; let `Λ` be its colimit.
The natural map `Λ -> Q` is the identity on each vertex. Then:

1. The link girths are `(6,8,6)`, so `Λ` is an infinite word-hyperbolic
   triangle group with embedded vertex groups.
2. Its kernel `N` is torsion-free of index `3420`, with a finite
   two-dimensional classifying complex having `3` vertices, `2052`
   edges and `3420` faces.
3. `H_1(N;Z)=0` and `H_2(N;Z)=Z^1370`. In particular `N` is perfect.

**Status:** exact computation plus written topological interpretation,
independently reviewed and fully reproduced on 2026-09-20; see Section 7
of `research/artifacts/hyperbolic-rf-wave2-audit-2026-09-20.md`.
No assertion about further finite covers or
residual finiteness follows merely from this calculation.

Proof and computational verification:
[[wave2-detector-psl19-perfect-first-kernel-proof]].
