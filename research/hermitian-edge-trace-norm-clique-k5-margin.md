---
rg: 2
id: hermitian-edge-trace-norm-clique-k5-margin
kind: claim
title: A Hermitian 5x5 matrix with zero diagonal and off-diagonal moduli at least 1 has trace norm at least 7.0857, above the clique bound 4 sqrt3 = 6.9282
artifacts:
  - research/hermitian-edge-trace-norm-clique-k5-margin-box-scheme.md
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hilane.sh
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hi_runs.log
distinct_from:
  hermitian-edge-trace-norm-clique-inequality-k5: that is c_5 >= 4 sqrt3 = 6.9282, the clique inequality; this is the strictly stronger c_5 >= 7.0857, which implies it.
  hermitian-edge-trace-norm-odd-antihole-c11: that is the antihole bound on the complement of C_11; this K_5 bound is the input that proves it.
---

**ESTABLISHED (computer-assisted; certificates checked in exact rational arithmetic; unreviewed,
not Lean-verified; route `hermitian-edge-trace-norm-clique-k5-margin-box-scheme`).**

**Theorem.** Every Hermitian `5 x 5` matrix `C` with `C_ii = 0` and `|C_ij| >= 1` for `i != j`
satisfies

```text
|| C ||_1  >=  7.0857 .
```

This exceeds `4 sqrt3 = 6.92820` by `0.1575` and `45 sqrt3/11 = 7.08566` by `4 * 10^-5`. The
numerical minimum is `c_5 = 5 + sqrt5 = 7.2361`, so the bound is within `2.1%` of the truth.

**Why it matters.** The margin `eps_5 = c_5 - 4 sqrt3 > 0` is what clique coverings need. Every
covering of a graph by `K_5`'s that falls short of `(**)` by less than the margin is closed by it:
- `C̄_11`: its eleven `K_5`'s give `||C||_1 >= (11/5) c_5 >= 9 sqrt3`
  (`hermitian-edge-trace-norm-odd-antihole-c11`);
- the webs `C_n^4`: their `n` windows give the rank inequality for every `n >= 10` except twelve
  values (`hermitian-edge-trace-norm-web-rank-k4`).

## Attempts

- 2026-09-18 (w7-078): proved by the `K_5` box scheme at the higher target, route
  `hermitian-edge-trace-norm-clique-k5-margin-box-scheme`. Each of the 16 slices took
  roughly twice the boxes of the `4 sqrt3` run (58.7k boxes per slice on average, 938614
  in all, 45002 s; `k5hi_runs.log`).
