---
rg: 2
id: ak3-two-tunnel-excursions-above-cap-24-proof
kind: route
title: Computation of the seeded 2-tunnel closure of AK(3) at cap 24, band (24, 26], by factoring the second AC product through Whitehead-minimal classes
target: ak3-two-tunnel-excursions-above-cap-24
requires: []
artifacts:
  - experiments/ak3-two-tunnel-closure-2026-09-17/README.md
  - experiments/ak3-two-tunnel-closure-2026-09-17/t2m.c
  - experiments/ak3-two-tunnel-closure-2026-09-17/iter.sh
  - experiments/ak3-two-tunnel-closure-2026-09-17/loop.sh
  - experiments/ak3-two-tunnel-closure-2026-09-17/calib16.log
  - experiments/ak3-two-tunnel-closure-2026-09-17/rank2-seeded.log
  - experiments/ak3-two-tunnel-closure-2026-09-17/rank3-seeded.log
---

States, moves, goals, tunnels, S_24 and T_24 are as in `ak3-aut-tunnel-closed-exhaustion`,
whose computation (`ak3-aut-tunnel-closed-exhaustion-proof`) gives T_24 as a dump. `t2m.c`
includes `tunnel.c` of that experiment. So the move generator, the canonical form, the cut-formula
Whitehead reduction and the goal tests are the same code.

## Step 1: the second level factors through classes

Let s be a state and t a tunnel from s whose greedy reduction stops at m, with 24 < |m| ≤ 26.
The 2-tunnels through t are the (M1) products of m, each followed by greedy reduction. They
depend only on m.

Replacing m by a signed permutation or a swap of it permutes those products. The reduced
endpoints may differ, but each lies in the same Aut(F)-orbit, and both are Whitehead-minimal
or both have length ≤ 24. Here is why membership in the base does not depend on the choice.

- Two reduced representatives of length ≤ 24 in one Aut-orbit are both Whitehead-minimal,
  because greedy reduction stops only at a minimum.
- By Whitehead's peak-reduction theorem, the two are joined by Whitehead moves of
  non-increasing, hence constant, length. Every intermediate state has length ≤ 24.
- The base is closed under capped (M2): T_24 by `ak3-aut-tunnel-closed-exhaustion`, and each
  later base by `grow`, which closes under capped moves.

So one pass over the distinct classes m covers every 2-tunnel. Mode A of `t2m` enumerates the
classes, and mode B applies all (M1) products to each class.

## Step 2: calibration

In rank 2 at cap 16 with C2 = 24, `grow2t.c` of the w6 experiment reports a 2-tunnel
closure of 161 states. `calib16.log` recomputes it with `t2m`:

1. Mode A on the 150-state T_16 gives 16575 classes.
2. Mode B lands 325 products, which fall into 7 canonical classes.
3. `grow` turns these into 11 states.
4. Mode B on the 1134 new classes from those 11 lands nothing.

The total is 161 states, the same as `grow2t`.

## Step 3: rank 2, seeded from the 922 tunnel-only states

`loop.sh 2 26 s24r2.txt empty.txt new922r2.txt r2r 1` runs `iter.sh` until a round adds nothing.
The first round was run by hand with the same commands. Every chunk exits 0, and all rounds
are in `rank2-seeded.log`.

| round | states in | new m classes | (M1) products | NEW landings (classes) | grown states |
|---|---|---|---|---|---|
| 1 | 922 | 4340 | 10,261,440 | 3209 (156) | 224 |
| 2 | 224 | 1154 | 2,604,440 | 1679 (81) | 131 |
| 3 | 131 | 722 | 1,617,040 | 802 (38) | 53 |
| 4 | 53 | 311 | 698,200 | 124 (8) | 17 |
| 5 | 17 | 87 | 199,060 | 0 (0) | 0 |

In every round, every count below is 0:

- PRIM endpoints of (M1) products from m;
- PRIM or THICK among the classes m themselves (each m gets `is_primitive` on both entries and
  `thick2` after the planarity prefilter, with 0 undecided);
- PRIM or THICK among grown states;
- PRIM endpoints of tunnels from grown states.

`grow` closes each round's landings under capped moves and tunnels. So the final set is closed
under capped moves, tunnels, and 2-tunnels from every state outside S_24:

- the 922 seeds and all 425 added states were run through mode A;
- the 6614 classes were run through mode B.

This set is U_24, with 262642 + 425 = 263067 states.

## Step 4: rank 3, seeded from the 1714 tunnel-only states

`CHUNK=800 loop.sh 3 26 s24r3.txt empty.txt new1714r3.txt r3r 1` runs with the same tools in
rank 3, where the automorphisms are the 90 Whitehead automorphisms. It makes 16 mode-B chunks,
all exit 0, and every step is in `rank3-seeded.log`.

| round | states in | new m classes | (M1) products | NEW landings (classes) | grown states |
|---|---|---|---|---|---|
| 1 | 1714 | 8148 | 25,699,856 | 3209 (156) | 224 |
| 2 | 224 | 1154 | 3,646,216 | 1679 (81) | 131 |
| 3–5 | 131, 53, 17 | 722, 311, 87 | 3,520,020 | 926 (46) | 53, 17, 0 |

The goal tests are those of Step 3 plus PROJ, which in rank 3 is `goal()` with primitivity
switched off. All counts are 0. The m classes took 30588 Neuwirth tests, with 0 undecided.
The closure has 281927 + 425 = 282352 states.

## What is not covered

Mode A was not run on S_24 itself, so 2-tunnels whose first product starts inside S_24 are not
covered. Neither are intermediate points of length 27 or more, or chains of three or more
products inside the band. `band.sh` explores those chains, and the target records them as
not claimed.
