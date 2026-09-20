---
rg: 2
id: wave5-detector-psl19-square-kernel-mod-three-acyclicity
kind: claim
title: The specified PSL2(19)-squared kernel has zero first mod-three homology and excludes every three-and-five refinement
distinct_from:
  wave4-detector-psl19-square-kernel-mod-five-acyclicity: coefficient-three control is additional and rules out mixed solvable kernels with only three and five as prime divisors
artifacts:
  - research/artifacts/hyperbolic-rf-wave5-detectors-2026-09-20.md
  - experiments/hrf-wave5-detectors-2026-09-20/c5/tensor_homology.py
  - experiments/hrf-wave5-detectors-2026-09-20/c5/tensor_homology_result.json
  - experiments/hrf-wave5-detectors-2026-09-20/c5/generator.py
  - experiments/hrf-wave5-detectors-2026-09-20/c5/generator_result.json
---

For the exact map `Λ→Q²`, `Q=PSL_2(19)`, constructed in
[[wave2-detector-psl19-has-second-simple-quotient]], let `M` be its
kernel. Then `H_1(M;F_3)=0` and `dim H_2(M;F_3)=4,688,819`.

Together with [[wave4-detector-psl19-square-kernel-mod-five-acyclicity]],
this implies that `M` has no nontrivial finite image whose
prime divisors lie in `{3,5}`. The same holds for each preimage `M_c`
in a nonzero central five-twist. Consequently refinements
of this specified `Q²` quotient using only those two primes cannot
detect a twist center. Removing the solvability hypothesis here uses
the classical Burnside theorem for finite groups of order `3^a5^b`.

Other primes and arbitrary nonsolvable refinements remain uncontrolled.
Integral perfectness and hyperbolic residual finiteness remain open.

**Status:** complete exact computation and independent mathematical/source
review PASS on2026-09-20. The generator, full largest tensor and module
certificates were independently replayed; all25 output identities were
checked. The remaining24 tensor ranks were source/output reviewed, not
all independently recomputed. No proof-assistant certification is claimed.

Proof: [[wave5-detector-psl19-square-kernel-mod-three-proof]].
