---
rg: 2
id: distance-code-leakage-bounds-phase-energy
kind: claim
title: Leakage delta from a label-diagonal code changes normalized energy by at most square root delta
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
distinct_from:
  distance-code-local-tests-are-label-diagonal: That proves exact vanishing of off-diagonal compressed blocks; this bounds expectation changes for states with leakage outside the code.
---

Let P be a computational-basis code projector tensored with arbitrary
auxiliary identity, and let 0<=K<=I have label-diagonal compression PKP.
For every density matrix rho with Tr(P rho)>=1-delta, 0<=delta<1,
there is a code-supported state sigma dephased in the logical label
such that |Tr(K rho)-Tr(K sigma)|<=sqrt(delta).

In particular this holds for sums of tests below the classical code
distance. Normalization is essential: the bound is for a positive
contraction. Small code leakage supplies this controlled error, not
a constant-strength replacement phase check.

