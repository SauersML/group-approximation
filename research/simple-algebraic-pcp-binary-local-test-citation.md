---
rg: 2
id: simple-algebraic-pcp-binary-local-test-citation
kind: route
title: Import the composition-free constant-query binary algebraic PCP
target: simple-algebraic-pcp-binary-local-test
requires: []
artifacts:
  - research/artifacts/two-august-2026-anti-localization-papers-2026-08-20.md
---

**Established by citation.**  Amireddy--Behera--Srinivasan--Sudan--Willumsgaard,
arXiv:2608.17429v1, construct a polynomial-size proof for graph 3-coloring
which is verified with logarithmic randomness and a constant number of binary
queries, without PCP composition.

Theorem 4.1 gives their constant-query low-degree test over `F_2`; low
rejection forces proximity to the low-degree Hadamard encoding stated there.
Theorem 5.1 gives constant-query local correction with error
`O_c(d_1/q+eta+delta)`.  Their zero-on-grid test and the full verifier in
Appendix E assemble these ingredients into the PCP theorem.

This imports a Hamming/proof-oracle soundness theorem.  It does not supply
commuting proof-coordinate projections or group-word payment in arbitrary
normalized-HS microstates.
