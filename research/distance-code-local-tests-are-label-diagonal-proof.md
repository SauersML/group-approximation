---
rg: 2
id: distance-code-local-tests-are-label-diagonal-proof
kind: route
title: Proof of tests below classical code distance have label-diagonal compression even with shared quantum auxiliaries
target: distance-code-local-tests-are-label-diagonal
requires: []
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
---

For distinct codewords, at least one differing bit is outside
each operator's data support; the corresponding inner product is zero,
even as an operator-valued matrix element on the auxiliary space.
Sum these identities. The compression is block diagonal, proving
energy invariance under label dephasing. In the repetition example
the target phase projector has off-diagonal entry -1/2 while the
compression has zero; operator norm bounds that entry. I/2 attains
the lower bound. Section 3.3 gives the complete proof.

