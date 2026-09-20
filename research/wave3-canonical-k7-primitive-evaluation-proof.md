---
rg: 2
id: wave3-canonical-k7-primitive-evaluation-proof
kind: route
title: Compute the three stabilizer abelianizations and use the cyclic augmentation socle in the integral homology spectral sequence
target: wave3-canonical-k7-class-has-primitive-evaluation
requires:
  - cckw-ghb2-kms-group-structure
  - ghb7-triangle-vertex-groups-split-abelianizations
artifacts:
  - research/artifacts/hyperbolic-rf-wave3-canonical-class-2026-09-20.md
  - experiments/hrf-wave3-canonical-class-2026-09-20/stabilizers.py
  - experiments/hrf-wave3-canonical-class-2026-09-20/stabilizers.json
---

The artifact supplies the complete integral proof. The kernel of the
orbit homology differential D->(C7)^6 contains 7D and has nonzero
reduction modulo seven, since H1(K) surjects C7^2. Deck equivariance
forces that reduction to contain the all-ones socle vector in the
augmentation module. Face-zero evaluation is therefore coprime to
seven while its ideal contains seven, so is primitive. The finite
central-image restriction follows directly from the homology five-term
sequence and the central generator's membership in the commutator.
