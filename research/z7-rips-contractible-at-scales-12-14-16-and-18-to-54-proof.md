---
rg: 2
id: z7-rips-contractible-at-scales-12-14-16-and-18-to-54-proof
kind: route
title: Check the slack-one partition criterion for n = 7 at r = 12, 14, 16 and 18..54
target: z7-rips-contractible-at-scales-12-14-16-and-18-to-54
requires: [zn-rips-slack-sphere-criterion]
artifacts: [experiments/zn-rips-slack-sphere-2026-09-18/README.md, experiments/zn-rips-slack-sphere-2026-09-18/slack_crit.cpp, experiments/zn-rips-slack-sphere-2026-09-18/slack_crosscheck.py, experiments/zn-rips-slack-sphere-2026-09-18/results.txt]
---

By `zn-rips-slack-sphere-criterion`, it suffices to check two things for `n = 7` and each listed `r`:
1. every unbalanced partition of `r` into at most 7 parts has exactly 7 parts;
2. each such partition `x` has a slack-one dominator at every index `k`.

`slack_crit.cpp` does this check exhaustively (`./slack_crit 7 10 54`). The method is in §4 of
`zn-rips-slack-sphere-criterion-proof`. Section A of `results.txt` has the output. For every `r` in the claim, it
prints `without-y=0`, which means every pair `(x, k)` has a certified `y`.

| r | unbalanced partitions (all with 7 parts) | pairs (x, k) checked |
|---|---|---|
| 12 | 3 | 9 |
| 14 | 4 | 13 |
| 16 | 2 | 8 |
| 18 | 1 | 5 |
| 19 | 14 | 56 |
| 21 | 17 | 74 |
| 23 | 12 | 58 |
| 25 | 14 | 71 |
| 27 | 10 | 51 |
| 29 | 6 | 36 |
| 31 | 3 | 19 |
| 33 | 3 | 17 |
| 35 | 1 | 7 |

- For even `20 ≤ r ≤ 34` and for `36 ≤ r ≤ 54`, `U(7,r)` is empty, and the hypothesis holds vacuously. This agrees
  with `z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54`, which was computed by a separate program.
- The unbalanced counts agree with that program's `sphere_nop` counts.
- At `r = 10, 11, 13, 15, 17`, the program reports a 6-part unbalanced partition, and these scales are excluded.

Independent check. `slack_crosscheck.py` recomputes step 4 in numpy for every listed `r` with `U(7,r)` nonempty. It
takes the program's `U(7,r)` as input, materializes every signed arrangement `z` with `z_k > 0`, and uses a different
candidate order for `y`. It finds a certified `y` for every `(x, k)`. Section B of `results.txt` has the output.

The claim follows from `zn-rips-slack-sphere-criterion`. ∎
