---
rg: 2
id: wave4-detector-psl19-borel-a4-sector-vanishes
kind: claim
title: The Borel-times-A4 invariant sector of the specified PSL2(19)-squared kernel has zero first mod-five cohomology
distinct_from:
  wave3-detector-psl19-square-kernel-retains-five-twists: twist retention at M does not compute its first cohomology; this computes a specified invariant sector only
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-detectors-2026-09-20.md
  - experiments/hrf-wave4-detectors-2026-09-20/borel_a4_homology.py
  - experiments/hrf-wave4-detectors-2026-09-20/borel_a4_homology_result.json
---

Use the explicit epimorphism `f=(f_0,f_1):Λ→Q²`, `Q=PSL_2(19)`,
from [[wave2-detector-psl19-has-second-simple-quotient]], and let `M=ker f`.
Let `B≤Q` stabilize infinity on the projective line, and let `A≤Q`
be the subgroup of order twelve explicitly specified in the proof.
For `K=f^-1(B×A)`,

`dim H_1(K;F_5)=0`, `dim H_2(K;F_5)=2288`, and
`H¹(M;F_5)^(B×A)=0`.

This excludes only the indicated invariant sector. It does not show
`H_1(M;F_5)=0`, rule out every solvable refinement, or settle residual
finiteness. The computation and subgroup-to-module interpretation were
independently reviewed and the full script replayed on 2026-09-20.

Proof: [[wave4-detector-psl19-borel-a4-sector-proof]].
