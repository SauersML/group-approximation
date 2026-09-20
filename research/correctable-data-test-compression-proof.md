---
rg: 2
id: correctable-data-test-compression-proof
kind: route
title: Expand the auxiliary test in a data-operator basis and compress by exact error correction
target: correctable-data-tests-are-logically-blind
requires: []
artifacts:
  - research/artifacts/qpcp-integration-ledger-2026-09-20.md
---

The exact erasure-correction condition implies `E*O E=c_O I` for every
operator `O` supported on the erased region. One way to see this is that
the erased subsystem has the same density matrix on every encoded pure
state; applying polarization to its expectation of `O` makes the
compressed operator scalar. Equivalently this is the Knill–Laflamme
condition applied to all errors on that region; see
[Knill–Laflamme, A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034).

Expand `g=sum_j O_j tensor B_j` in an operator basis on the tested data
region. Then

```text
(E* tensor I)g(E tensor I)
  = sum_j (E*O_jE) tensor B_j
  = I tensor sum_j c_(O_j) B_j.
```

Compression by an isometry preserves positivity and the upper bound by
identity, proving the claim for positive-contraction tests. Taking trace
against any logical-plus-auxiliary state leaves only its auxiliary marginal.
Linearity proves the assertion for sums of tests.
