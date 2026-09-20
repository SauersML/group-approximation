---
rg: 2
id: thompson-f-census-witnesses-have-frozen-trace-spread-computation
kind: route
title: Replay the S_8 trace profiles, the commutant block split and the constrained restarts on the stored witnesses
target: thompson-f-census-witnesses-have-frozen-trace-spread
requires: []
artifacts:
  - research/artifacts/thompson-f-census-trace-spread-2026-09-17.md
  - experiments/thompson-f-witness-trace-test-2026-09-17/words6.py
  - experiments/thompson-f-witness-trace-test-2026-09-17/blocks.py
  - experiments/thompson-f-witness-trace-test-2026-09-17/check_classes.py
  - experiments/thompson-f-witness-trace-test-2026-09-17/constrained_census.py
  - experiments/thompson-f-witness-trace-test-2026-09-17/impose.sh
---

This is a direct computation in float64. The per-item replay commands and outputs are in the artifact, Section 2.
All commands run in `experiments/thompson-f-witness-trace-test-2026-09-17/`.

- **Item 1:** `python3 check_classes.py 8` (exact over `Q`), then
  `python3 words6.py 8 wit_F_n16.npy wit_F_n32.npy wit_F_n64b.npy wit_F_n128.npy`.
- **Item 2:** `python3 blocks.py wit_F_n16.npy 5 0.05`, `python3 blocks.py wit_F_n32.npy 9 0.02` and
  `python3 blocks.py wit_F_n64.npy 17 0.01` and `python3 blocks.py wit_F_n64b.npy 20 0.01`.
- **Item 3:** `sh impose.sh`.

**Trust surface.**
- The trace values in item 1 are sums of at most 8 products of unitary matrices of size at most 128, so the float64
  error is far below the reported margins.
- The blocks in item 2 are numerical. Their leakage is printed, and the ratio of each core matches the ratio of
  the whole witness to 3 digits.
- Item 3 records optimizer outcomes, which are upper bounds on `D_n` only.
