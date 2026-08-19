---
rg: 2
id: literal-clifford-ce-model-proof
kind: route
title: Build the finite-coset Clifford tower and its automorphic dilation
target: literal-clifford-ce-model
requires: []
artifacts:
  - notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md
  - GroupApproximation/Sofic/RadicalSeparation.lean
---

The source note gives the complete construction.  On
`X_n = Gamma / beta^n(Gamma)`, finite Clifford stages crossed by `Gamma` are
Connes embeddable and exhaust the core.  Its trace-preserving endomorphism
has a Connes-embeddable automorphic dilation.  In the final crossed product,
the literal generators map to `u_delta`, the implementing unitary `U`, and
`U^* C_x U`; the two distinguished Majoranas are at different coset sites,
so their commutator is exactly `-1`.

The countable image is therefore a hyperlinear detector of `w`.  The semantic
conversion from a detector to non-membership in the hyperlinear residual is
kernel-checked in `RadicalSeparation.lean`.
