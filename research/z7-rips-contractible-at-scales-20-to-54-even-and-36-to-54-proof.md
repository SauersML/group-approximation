---
rg: 2
id: z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54-proof
kind: route
title: Every partition of r into at most seven parts is balanced at these scales, by exhaustive enumeration
target: z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54
requires: [zn-rips-sphere-balanced-dominator-criterion]
artifacts: [experiments/zn-rips-sphere-core-2026-09-17/README.md, experiments/zn-rips-sphere-core-2026-09-17/sphere_nop.cpp, experiments/zn-rips-sphere-core-2026-09-17/results.txt]
---

By `zn-rips-sphere-balanced-dominator-criterion`, it suffices to check that every partition of `r` into
`s ≤ 7` positive parts is balanced. A partition `x` is balanced if some integer `y` with `0 ≤ y ≤ x` and
`y ∉ {0, x}` has `⟨σ,y⟩` between `0` and `⟨σ,x⟩` for all `σ ∈ {±1}^s`.

`experiments/zn-rips-sphere-core-2026-09-17/sphere_nop.cpp` enumerates, for each `s` and `N`, all partitions of
`N` into exactly `s` parts. It certifies balance either via `x/gcd(x)`, or by finding an explicit `y` and checking all
`2^s` sign vectors. When no quick witness exists, it searches the whole box `0 ≤ y ≤ x`, `1 ≤ |y| ≤ ⌊N/2⌋`. This
search is complete because `y ↦ x − y` preserves balance.

Output (`results.txt`, runs `./sphere_nop s 1 54` for `s = 1..7`): the only sums `N ≤ 54` that have an unbalanced
partition into `s` parts are
- `s = 1`: `1`;
- `s = 2`: `2`;
- `s = 3`: `3`;
- `s = 4`: `4, 5`;
- `s = 5`: `5, 6, 7, 9`;
- `s = 6`: `6–11, 13, 15, 17`;
- `s = 7`: `7–19, 21, 23, 25, 27, 29, 31, 33, 35`.

So for `r ∈ {20, 22, …, 34} ∪ [36, 54]` no partition of `r` into at most 7 parts is unbalanced, and the criterion
gives contractibility. For instance, at `r = 54` there are 13534 partitions with 7 parts, all balanced.

The unbalanced partitions at the odd scales `21..35` are listed in `results.txt`. At `r = 35` the only one is
`(8,7,6,5,4,3,2)`, and at `r = 33` they are `(9,8,5,4,3,2,2)`, `(9,7,6,4,4,2,1)` and `(7,6,5,5,4,3,3)`. At those
scales the criterion is silent, and nothing is claimed there.
