---
rg: 2
id: z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70-proof
kind: route
title: Check the slack-one partition criterion for n = 8 at every even r in 20..36 and every r in 37..70
target: z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70
requires: [zn-rips-slack-sphere-criterion]
artifacts: [experiments/zn-rips-slack-sphere-2026-09-18/README.md, experiments/zn-rips-slack-sphere-2026-09-18/slack_crit.cpp, experiments/zn-rips-slack-sphere-2026-09-18/slack_shard.cpp, experiments/zn-rips-slack-sphere-2026-09-18/u_only.cpp, experiments/zn-rips-slack-sphere-2026-09-18/U8.txt, experiments/zn-rips-slack-sphere-2026-09-18/results.txt]
---

By `zn-rips-slack-sphere-criterion`, it suffices to check two things for `n = 8` and each listed `r`:
1. every unbalanced partition of `r` into at most 8 parts has exactly 8 parts;
2. each such partition `x` has a slack-one dominator at every index `k`.

The method is §4 of `zn-rips-slack-sphere-criterion-proof`. Section E of `results.txt` has the output.

- **Even `38 ≤ r ≤ 70`.** `U(8,r)` is empty (`z8-rips-contractible-at-even-scales-38-to-70`), and the hypothesis
  holds vacuously.
- **Odd `59 ≤ r ≤ 69`.** Checked by `./slack_crit 8 r r`.
- **Odd `37 ≤ r ≤ 57` and even `20 ≤ r ≤ 36`.** Checked in two steps.
  1. `u_only.cpp` writes `U(8,r)` to `U8.txt`. It has the same code for `U` as `slack_crit.cpp`.
  2. `slack_shard.cpp` (`./slack_shard 8 r U8.txt s S`) checks the partitions `x` with index `≡ s (mod S)` against
     all of `U(8,r)`. It has the same dominator search as `slack_crit.cpp`, plus one more exact pruning bound: each
     coordinate adds at most `x_i − y_i` to `(|z−y| − |z|) − (|z−x| − |z|)`, which must reach `1`. Each run exits
     with code 1 if some partition in `U` has fewer than 8 parts, or if some `(x, k)` has no dominator.

  All 227 shard runs exit with code 0 and `without-y=0`.

| r | unbalanced partitions (all with 8 parts) | pairs (x, k) checked |
|---|---|---|
| 69 | 11 | 88 |
| 67 | 22 | 170 |
| 65 | 29 | 218 |
| 63 | 32 | 243 |
| 61 | 48 | 364 |
| 59 | 66 | 492 |
| 57 | 79 | 571 |
| 55 | 100 | 717 |
| 53 | 110 | 791 |
| 51 | 125 | 865 |
| 49 | 155 | 1057 |
| 47 | 157 | 1048 |
| 45 | 186 | 1203 |
| 43 | 170 | 1084 |
| 41 | 180 | 1132 |
| 39 | 177 | 1062 |
| 37 | 182 | 1055 |

| r | unbalanced partitions (all with 8 parts) | pairs (x, k) checked |
|---|---|---|
| 36 | 1 | 8 |
| 34 | 3 | 19 |
| 32 | 4 | 26 |
| 30 | 7 | 43 |
| 28 | 10 | 55 |
| 26 | 16 | 82 |
| 24 | 12 | 60 |
| 22 | 18 | 79 |
| 20 | 14 | 57 |

The unbalanced counts at odd `37 ≤ r ≤ 57` agree with the independent `sphere_nop` and `sphere_nop2` counts recorded in
`experiments/zn-rips-sphere-core-2026-09-17/results.txt`.

The claim follows from `zn-rips-slack-sphere-criterion`. ∎
