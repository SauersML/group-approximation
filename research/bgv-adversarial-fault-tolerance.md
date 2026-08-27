---
rg: 2
id: bgv-adversarial-fault-tolerance
kind: claim
title: Joint subsystem-product coding withstands almost-linear adversarial corruption
artifacts:
  - research/artifacts/two-august-2026-anti-localization-papers-2026-08-20.md
distinct_from:
  clifford-hs-defect-becomes-adversarial-site-noise: that asks to manufacture a tensor-site noise model from arbitrary HS microstates; this theorem assumes the physical tensor sites and adversarial support are already given.
---

For every fixed prime-power physical alphabet and every positive overhead
slack, sufficiently large logical circuits admit a constant-alphabet
fault-tolerant compilation with polynomial space, subpolynomial depth
overhead, and tolerance against arbitrary corruptions on

```text
N / 2^(O(sqrt(log Nbar))) = N^(1-o(1))
```

physical qudits per time step.  The construction jointly encodes the logical
qudits in high-rate, high-distance subsystem-product codes and recursively
reduces the physical alphabet.

The exact hypotheses and parameters are imported by
`bgv-adversarial-fault-tolerance-citation`.
