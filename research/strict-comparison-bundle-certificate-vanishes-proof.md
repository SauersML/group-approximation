---
rg: 2
id: strict-comparison-bundle-certificate-vanishes-proof
kind: route
title: Subequivalence in the tracial ultrapower with zero trace defect gives equivalence, lifted back into the completion
target: strict-comparison-bundle-certificate-vanishes
requires:
  - strict-comparison-compares-ultrapower-projections
artifacts:
  - research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md
---

Section 6 of the artifact.

1. **Embedding.** The unit ball of `M_k(A)` is `‖·‖_{2,u}`-dense in that of
   `M_k(M)`. So `M_k(M)` embeds in `M_k(A^ω)`, and `P` and `Q` agree on every limit
   trace.
2. **Subequivalence.** The prerequisite gives `v` with `v*v = P` and `vv* ≤ Q`.
3. **Equivalence.** The projection `Q − vv*` vanishes on every limit trace. Take
   traces that nearly attain its uniform 2-norm. Their limit trace equals the
   square of that norm, so the norm is zero and `vv* = Q`.
4. **Lift.** Lift `v` to contractions `v_n`. Then `W_n = Q v_n P` represents `v`, so
   both defects tend to zero along `ω`.
