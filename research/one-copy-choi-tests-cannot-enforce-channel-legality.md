---
rg: 2
id: one-copy-choi-tests-cannot-enforce-channel-legality
kind: claim
title: One-copy Hermitian tests accepting every unitary Choi state also accept an invalid product state
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
---

For input and output dimension D>=2, let
|J_U>=D^(-1/2)sum_j |j> tensor U|j>.
If a Hermitian K on the single Choi register has energy <=eta
on every unitary Choi vector, some computational-basis product
state has energy <=eta. Its input marginal has trace distance
1-1/D from I/D. If K>=0 and eta=0, then K=0.

This holds without locality restrictions and with any fixed
channel-independent auxiliary state. It does not cover channel-dependent
auxiliary proofs, independently promised copies, or a problem-specific
restricted accepted family. In particular it constrains one proposed
static channel compiler, not the interactive QMA oracle-proof theorem
or all QPCP constructions.

