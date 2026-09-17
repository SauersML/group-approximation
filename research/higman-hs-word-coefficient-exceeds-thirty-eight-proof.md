---
rg: 2
id: higman-hs-word-coefficient-exceeds-thirty-eight-proof
kind: route
title: Replay two committed integer Cayley witnesses in exact Q(i) arithmetic
target: higman-hs-word-coefficient-exceeds-thirty-eight
requires: []
artifacts:
  - experiments/higman-hs-microstate-scaling-2026-09-17/certify_ratio_witness.py
  - experiments/higman-hs-microstate-scaling-2026-09-17/ratio_witness_cycle4_d6.json
  - experiments/higman-hs-microstate-scaling-2026-09-17/ratio_witness_cycle3_d6.json
  - experiments/hs_word_certificate.py
---

Each JSON witness stores integer rows of 36 Cayley parameters per
generator (denominator 1024). `hs_word_certificate.cayley` turns them into
`K` skew-Hermitian over `Q(i)` and `U=(I-K)(I+K)^(-1)`, which is exactly unitary.
`hs_word_certificate.check` recomputes, with `Fraction` arithmetic only, the
normalized energies of the marked generator and of every relator word, and
the strict margin `e(g_0)-C sum e(r_j)`.

- Four-cycle, `C=38`: `e(g_0)=2.47988...` and `sum e(r_j)=0.0640261...`, margin `0.0469 > 0`.
- Three-cycle, `C=10`: `e(g_0)=2.60953...` and `sum e(r_j)=0.252828...`, margin `0.0813 > 0`.

Any valid inequality `e(g_0)<=C sum e(r_j)` in dimension 6 would force a
nonpositive margin. So `C>38` and `C>10` respectively.

Replay: `python3 experiments/higman-hs-microstate-scaling-2026-09-17/certify_ratio_witness.py`
(default mode rebuilds from the integers and compares byte-for-byte), or
`python3 experiments/hs_word_certificate.py verify <witness.json>`. The
floating-point optimizer only produced the integers. `--derive` regenerates
them from the stored `.npz` optimizer outputs.
