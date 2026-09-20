---
rg: 2
id: wave4-canonical-class-five-finite-detector-proof
kind: route
title: Verify the explicit 28-dimensional Lie witness and apply its six marked face equations
target: wave4-canonical-prime-seven-class-virtually-splits
requires:
  - wave4-visibility-k7-marked-face-presentation
  - wave4-canonical-centre-dies-in-class-four-quotients
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-class-five-detector-2026-09-20.md
  - experiments/hrf-wave4-four-generator-2026-09-20/class_five_lie_witness.json
  - experiments/hrf-wave4-four-generator-2026-09-20/verify_finite_witness.py
  - experiments/hrf-wave4-four-generator-2026-09-20/finite_witness_verification.json
---

The standalone checker verifies all Lie axioms, nilpotency class5,
generation, vertex relations, six marked BCH face equations, and a
nonzero central mark. Lazard gives a finite group of order7^28 and a
surjection from the exactly marked integral cover detecting z with
order7. Its central quotient induces K7->F/<image(z)>, whose kernel
has index7^27. The kernel of the finite map from B_c0/<z^7> is a section
over that subgroup. The previously proved class-four vanishing makes
the lower-central position of z sharp. The artifact gives the proof
and keeps this single finite order distinct from unbounded visibility.
