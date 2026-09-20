---
rg: 2
id: wave4-detector-psl19-square-kernel-mod-five-acyclicity
kind: claim
title: The specified intersection of the two PSL2(19) kernels has zero first mod-five homology and admits no five-group refinement
distinct_from:
  wave3-detector-psl19-square-kernel-retains-five-twists: that proves the three central twists survive M; this computes all first mod-five homology of M through a verified projective generator
  wave4-detector-psl19-borel-a4-sector-vanishes: that excludes one invariant sector; this excludes the whole module
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-detectors-2026-09-20.md
  - experiments/hrf-wave4-detectors-2026-09-20/projective_summands.json
  - experiments/hrf-wave4-detectors-2026-09-20/tensor_homology.py
  - experiments/hrf-wave4-detectors-2026-09-20/tensor_homology_result.json
  - experiments/hrf-wave4-detectors-2026-09-20/a4_generator.py
  - experiments/hrf-wave4-detectors-2026-09-20/a4_generator_result.json
---

For the exact epimorphism `f=(f_0,f_1):Λ→PSL_2(19)²` constructed in
[[wave2-detector-psl19-has-second-simple-quotient]], put `M=ker f`.
Then `H_1(M;F_5)=0` and `dim H_2(M;F_5)=4,688,819`.

Consequently every finite quotient refinement over this specified
`PSL_2(19)²` quotient whose kernel is a five-group has trivial kernel.
For every nonzero central five-twist `Λ_c`, its preimage `M_c` of `M`
also has `H_1(M_c;F_5)=0`, and the corresponding five-group refinement
cannot detect its central generator.

This is not an integral perfectness statement. It does not exclude
mixed-prime solvable kernels or arbitrary further nonsolvable
quotients, and does not solve residual finiteness.

**Status:** full written proof and exact finite computations independently
reviewed PASS on2026-09-20. The reviewer replayed the32 intertwining
checks, all64 tensor sectors, and the full group-algebra generator
closure. No proof-assistant certification is claimed.

Proof: [[wave4-detector-psl19-square-kernel-mod-five-proof]].
