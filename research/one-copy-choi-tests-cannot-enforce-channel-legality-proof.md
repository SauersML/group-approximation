---
rg: 2
id: one-copy-choi-tests-cannot-enforce-channel-legality-proof
kind: route
title: Proof of one-copy hermitian tests accepting every unitary choi state also accept an invalid product state
target: one-copy-choi-tests-cannot-enforce-channel-legality
requires: []
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
---

The generalized shift-and-phase unitaries give a complete orthonormal
Choi basis whose projectors average to I/D^2. Thus Tr(K)/D^2<=eta.
Computational-basis product states have the same average, so one has
energy at most eta. Its marginal differs from I/D with eigenvalues
1-1/D and -1/D (multiplicity D-1). For positive K and eta=0,
zero trace implies K=0. A fixed auxiliary state induces an operator
on the Choi register to which the same proof applies.
Section 5 supplies the full argument and causal-normalization boundary.

