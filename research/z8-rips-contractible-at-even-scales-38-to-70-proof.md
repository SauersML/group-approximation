---
rg: 2
id: z8-rips-contractible-at-even-scales-38-to-70-proof
kind: route
title: Every partition of an even r in 38..70 into at most eight parts is balanced, by exhaustive enumeration
target: z8-rips-contractible-at-even-scales-38-to-70
requires: [zn-rips-sphere-balanced-dominator-criterion]
artifacts: [experiments/zn-rips-sphere-core-2026-09-17/README.md, experiments/zn-rips-sphere-core-2026-09-17/sphere_nop.cpp, experiments/zn-rips-sphere-core-2026-09-17/sphere_nop2.cpp, experiments/zn-rips-sphere-core-2026-09-17/results.txt]
---

By `zn-rips-sphere-balanced-dominator-criterion`, `VR(Z^8, d_1; r)` is contractible once every partition of `r`
into `s ≤ 8` positive parts is balanced. `experiments/zn-rips-sphere-core-2026-09-17/sphere_nop.cpp` decides balance
exhaustively for all partitions of `N` into exactly `s` parts (criterion route §5, README). `sphere_nop2.cpp` is the
same program with one extra stage: before the complete search it tries the scaled candidates
`y = ⌊xt/N⌋, ⌈xt/N⌉, round(xt/N)` for `t = 1..N−1`. Every candidate is verified by the same all-sign-vector test, so
a partition is still declared unbalanced only after the complete search fails. The verdicts are unchanged, and it
reproduces `sphere_nop` exactly on `s = 8`, `N = 30..37` (Sections C and J of `results.txt`) and on even `N = 38..50` and `54` (Sections C, H and I).

The runs in `results.txt` give `bad=0` at every even `N` with `38 ≤ N ≤ 70`, for every `s ≤ 8`:
- `s ≤ 6`: `./sphere_nop s 1 54` gives no unbalanced partition with `N ≥ 18` (Section A), and `./sphere_nop s 55 70`
  gives none (Section F);
- `s = 7`: `./sphere_nop 7 7 54` gives none with `N ≥ 36` (Section B). `./sphere_nop 7 55 70`, stopped after `N = 58`
  (Section F), and `./sphere_nop 7 N N` for even `N = 58..70` (Section G) give none;
- `s = 8`: `./sphere_nop2 8 N N` for even `N = 38..70` gives `bad=0` (97539 partitions at `N = 70`; Section H).
  `sphere_nop` confirms `N = 38, 40` (Section C) and `N = 42..50, 54` (Section I) independently.

So the criterion applies at every even `r ∈ [38, 70]`. At `r = 36` the partition `(8,7,6,5,4,3,2,1)` is
unbalanced, and at every odd `r` from 37 to 57 between 79 and 186 partitions are (Sections C and L). Nothing is claimed at those scales.
