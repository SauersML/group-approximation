---
rg: 2
id: ak3-no-short-primitive-relator-certificate
kind: claim
title: AK(3) has no primitive-relator certificate for one-stabilization AC-triviality through relator pairs of total length at most 24
distinct_from:
  one-stabilization-ac-trivial-from-primitive-relator: that proves a certificate suffices; this is an exhaustive negative for short certificates of AK(3)
  ak3-is-stably-ac-trivial: that is the open statement; this only rules out one bounded certificate class
artifacts:
  - experiments/ak3-stable-primitive-search-2026-09-17/pzsearch.c
  - experiments/ak3-stable-primitive-search-2026-09-17/pzbest.c
  - experiments/ak3-stable-primitive-search-2026-09-17/verify_chain.py
  - experiments/ak3-stable-primitive-search-2026-09-17/crosscheck_bfs.py
  - experiments/ak3-stable-primitive-search-2026-09-17/crosscheck-caps14-18.log
  - experiments/ak3-stable-primitive-search-2026-09-17/ak3-rank3-caps21-26.log
  - experiments/ak3-stable-primitive-search-2026-09-17/ak3-rank3-bestfirst-cap38.log
  - experiments/ak3-stable-primitive-search-2026-09-17/pzproj.c
  - experiments/ak3-stable-primitive-search-2026-09-17/filter_proj.py
  - experiments/ak3-stable-primitive-search-2026-09-17/pzsame.c
  - experiments/ak3-stable-primitive-search-2026-09-17/ak3-proj-cap20.log
  - experiments/ak3-stable-primitive-search-2026-09-17/ak3-proj-caps22-24.log
  - experiments/ak3-stable-primitive-search-2026-09-17/ak3-projection-rank2-membership.log
---

**Computed, exhaustive; caps ≤ 18 cross-checked by a second implementation; unreviewed.**

In F = F(x, y, z), let the start be the AK(3) pair (x³y⁻⁴, xyxy⁻¹x⁻¹y⁻¹). The
implemented move graph on relator pairs, taken up to cyclic rotation, inversion, order of
the pair and signed permutations of {x, y, z}, has these edges:

- **(M2)** apply one of the 90 Whitehead automorphisms of type 2 to both relators;
- **(M1)** replace r_i by the cyclic reduction of U·g·V·g⁻¹. Here U is a rotation of r_i,
  V is a rotation of r_j^{±1} (j ≠ i), and g is empty or a single letter.

Every edge is a composite of moves (P1)/(P2) of
`one-stabilization-ac-trivial-from-primitive-relator`.

**Claim.** Restrict to pairs with |r_1| + |r_2| ≤ 24, lengths cyclically reduced. The
component of the start contains no pair with a primitive relator.

**Component sizes.** The BFS closes the component at each cap with no goal:

| cap | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| states | 1 | 67 | 146 | 609 | 1110 | 3846 | 6875 | 23638 | 42161 | 146954 | 280213 |

Reproduce with `gcc -O3 -o pzsearch pzsearch.c && ./pzsearch 3 CAP 50000000 xxxYYYY xyxYXY`. Caps ≤ 20 were run interactively; caps 21–24 are in the log. Cap 24 closed at BFS depth 37 in 733s on a shared machine. Cap 25 did not finish within 1200s.

**Calibration.**
- The same code finds a goal for AK(2) at cap 13, and `verify_chain.py` independently
  verifies that certificate (two AC products, then a primitive relator).
- For the non-trivial pair (x², y³), caps 9, 11 and 13 close with no goal, as the Grushko
  argument in the proof route requires.

**Cross-check.** `crosscheck_bfs.py` recounts the component with the move code of
`verify_chain.py`, which shares no code with `pzsearch.c`. It marks all 48 symmetric images of a
pair as visited. For caps 14–18 it gives exactly the counts in the table, with no goal
(`crosscheck-caps14-18.log`). Caps 19–24 rest on `pzsearch.c` alone.

**Caveat.** The search uses a lossy cache of already-seen pairs. It only skips
re-insertion of a pair seen before, so it cannot hide a component element. Pair keys are
exact 128-bit packings.

**Meaning.**
- A one-stabilization certificate for AK(3) of this kind, if one exists, must pass through
  a pair of total length above 24.
- The Panteleev–Ushakov bound and Carreras' bottleneck-26 result concern the AC
  trivialization of AK(3) itself in rank 2. This result is about the weaker primitive
  goal in rank 3, with automorphisms allowed.

**Projections collapse to AK(3).** `pzproj.c` reruns the same BFS. For every pair and every
generator g with exponent-sum minor ±1, it forms the rank-2 projection P(r) of the projection form of
`one-stabilization-ac-trivial-from-primitive-relator`.
- Caps 20, 22 and 24 close with the same state counts as the table.
- The least projected total length is 13, attained only by AK(3) itself. So no projection
  has length ≤ 12, and none has a primitive relator.
- The cap-24 component has 162 distinct projections of total length ≤ 16.
  - `filter_proj.py` places 160 of them in the rank-2 component of AK(3) (AC moves and
    automorphisms of F_2, total length ≤ 18).
  - The other two, (x⁻³y⁻¹xy⁻², x⁻²y⁻²x⁻¹y⁻¹x²y) and (x⁻⁴y⁻¹x⁻¹y⁻¹, x⁻¹y⁻⁴x⁻¹y³), are in that
    component at cap 20. `pzsame.c` confirms this exactly.
- The rank-2 component of AK(3) has 6867, 41257 and 261720 pairs at caps 20, 22 and 24. The
  rank-3 counts are only slightly larger.

So, through total length 24, the one extra generator produces no short projection outside the
rank-2 class of AK(3). The stabilized move graph gives no shortcut at these lengths: every short
projection has one-stabilization AC-equivalent to AK(3)⁺. Projections of length 17–24 were not
classified. Logs: `ak3-proj-cap20.log`, `ak3-proj-caps22-24.log`,
`ak3-projection-rank2-membership.log`.

**Larger caps.** The best-first variant `pzbest.c` expands pairs in order of total length. At cap 38 it inserts about 750 new pairs per expanded pair. Within 1200s it expanded 2661 pairs, all of total length at most 19, so it decides nothing beyond the table. Bounded-length exhaustive search therefore stops being feasible near length 25.
