---
rg: 2
id: ak3-rank2-capped-component-at-total-length-26-proof
kind: route
title: Computation of the AK(3) capped component at cap 26 in rank 2 by a resumable breadth-first search with the move generator of thzsearch, then Neuwirth tests on the states outside S_24, and the same search in rank 3 compared with it
target: ak3-rank2-capped-component-at-total-length-26
requires: []
artifacts:
  - experiments/ak3-cap26-component-2026-09-17/README.md
  - experiments/ak3-cap26-component-2026-09-17/capbfs.c
  - experiments/ak3-cap26-component-2026-09-17/thkcheck.c
  - experiments/ak3-cap26-component-2026-09-17/run.sh
  - experiments/ak3-cap26-component-2026-09-17/thkrun.sh
  - experiments/ak3-cap26-component-2026-09-17/calib.log
  - experiments/ak3-cap26-component-2026-09-17/rank2-cap26.log
  - experiments/ak3-cap26-component-2026-09-17/rank2-cap28.log
  - experiments/ak3-cap26-component-2026-09-17/cmp28.py
  - experiments/ak3-cap26-component-2026-09-17/cmp28.log
  - experiments/ak3-cap26-component-2026-09-17/rank3-cap26.log
  - experiments/ak3-cap26-component-2026-09-17/rank3-cap24.log
  - experiments/ak3-cap26-component-2026-09-17/decomp.py
  - experiments/ak3-cap26-component-2026-09-17/rank3-decomp.log
  - experiments/ak3-cap26-component-2026-09-17/thick-cap26.log
  - experiments/ak3-cap26-component-2026-09-17/alex.py
  - experiments/ak3-cap26-component-2026-09-17/alex-s24.log
---

The states, moves, canonical form and goal tests are those of
`experiments/ak3-thick-z-pair-search-2026-09-17/thzsearch.c`. `capbfs.c` includes
`thzsearch.c` verbatim, with its `main` renamed. So the move generator, the canonical form
`canon_pair`, the state store and `is_primitive` are the same code as the search that
produced S_24. The inner loop of `capbfs.c` is the loop of thzsearch's `main`, unchanged.

## Step 1: what the search computes

- `canon_pair` sends a pair to a canonical representative of its class under swapping the
  entries, the signed permutations of the generators, rotation and inversion of each entry.
- The moves (M1) and (M2) commute with these symmetries: a symmetry carries each move from a
  state to a move from the image state. So the classes and the moves between them form a
  well-defined quotient graph, and breadth-first search on classes computes the component
  of the class of AK(3).
- A state is expanded once, when the queue head reaches it. Every (M2) image and every (M1)
  product of length ≤ 26 is inserted; inserting a class that is already present does
  nothing.
- The search stops when the queue head reaches the number of stored states. Then every
  stored state has been expanded, so the stored set is closed under capped moves. It is
  also connected to AK(3), since each state was inserted as a neighbour of an earlier one.
  So the stored set is S_26.
- The 8M-entry cache in `consider` only skips products that were seen just before. A skipped
  product was already inserted, so the cache does not change the result.

## Step 2: the checkpoints do not change the result

`capbfs` runs in slots of at most 1100 s. At the end of a slot it writes the header (number
of states, queue head, end of the current level, depth, count of PRIM tests) and the state
array, and it stops only at a queue head that is a multiple of 1024 before that head is
expanded. On resume it rebuilds the hash table from the state array and continues from the
same head. Insertion order is the same as in one uninterrupted run, so the result is too.

Calibration (`calib.log`):
- At cap 24 with 60 s slots (three slot ends), `capbfs` gives 261720 states. The dump is
  byte-identical to that of `THZ_DUMP=... thzsearch 2 24 4000000 xxxYYYY xyxYXY dump`, which is S_24.
- An uninterrupted `thzsearch 2 26` run, stopped during level 9, has 735028 states after
  level 8. `rank2-cap26.log` has the same count.

## Step 3: the run

`run.sh 2 26 33000000 c26` (`capbfs 2 26 33000000 xxxYYYY xyxYXY c26.ck`) took two slots
(`rank2-cap26.log`).
- It ends with `EXHAUSTED depth 46 states 1690039 processed 1690039`.
- It made 1690038 PRIM tests: every inserted state except the start. It found no primitive
  entry. `is_primitive` is greedy Whitehead reduction to length 1. By Whitehead's theorem a
  primitive word reduces greedily to length 1, so the test is exact.
- The length histogram is the table of claim item 1.

This proves items 1 and 3 and the PRIM part of item 2. The two states of length 13 are read
from the dump.

## Step 4: THICK

- S_24 was tested before. `experiments/ak3-thick-z-pair-search-2026-09-17/ak3-rank2-caps14-24.log`
  records 261720 Neuwirth tests, 0 undecided and no thickenable state.
- The 1428319 states of S_26 not in S_24 (file difference of the two dumps) were tested by
  `thkcheck` (`thkrun.sh`, chunks of 12000 states, two workers, `thick-cap26.log`).
- `thkcheck` calls thzsearch's `thick_pair`, the same Neuwirth test `thick2`. It first
  applies the planarity test of `experiments/ak3-aut-tunnel-closure-2026-09-17/tunnel.c`.
  In rank 2 the Whitehead graph has 4 vertices and is always planar, so every state was
  tested.
- `thick-cap26.log` has 120 chunks. Every chunk has exit 0, and their ranges cover lines
  0 to 1428319 of `new26.txt` with no gap or overlap. In total there are 1428319 states,
  1428319 `thick2` calls, 0 undecided, and no THICK or PRIM goal. The last line of the log
  records this.
- Calibration: on the first 20000 states of S_24, `thkcheck` makes 20000 tests with no
  thickenable state and 0 undecided, as in the log above.

This proves the THICK part of item 2.

## Step 5: item 4

Every line of the S_24 dump is a line of the S_26 dump. The remaining 1428319 lines have the
length distribution given in item 4, read from the file difference. A state of length ≤ 24
in S_26 but not in S_24 is joined to AK(3) by a path of capped moves at cap 26, and by no path
at cap 24. So every such path passes through a state of length 25 or 26.

## Step 6: item 5

`alex.py` computes Δ_i for each entry by Fox calculus.
- The exponent vector (p, q) of an entry is primitive, because the relator matrix of a
  presentation of the trivial group is unimodular.
- G_i → Z sends x ↦ t^a and y ↦ t^b with (a, b) = (q, −p).
- The fundamental formula D_x (t^a − 1) + D_y (t^b − 1) = 0 gives
  Δ_i = D_y (t − 1)/(t^a − 1) when a ≠ 0, up to units ±t^k, and symmetrically when a = 0.
- Calibration: AK(3) gives t⁶ − t⁵ + t³ − t + 1 (the (3,4) torus knot) and t² − t + 1 (the
  trefoil). The basis pair gives 1 and 1.

`alex-s24.log` has the head of the histogram over S_24 and the 17 states with Δ_1 = Δ_2 = 1.
The last paragraph of item 5 then follows, because every state of S_24 is joined to AK(3) by
moves (M1) and (M2).

## Step 7: item 6 (rank 3)

- `run.sh 3 26 20000000 r3c26` and `run.sh 3 24 4000000 r3c24` run the same `capbfs`
  with RANK 3. There are 48 signed permutations and 90 Whitehead automorphisms, as in the
  rank-3 runs of thzsearch. Steps 1 and 2 apply unchanged.
- `rank3-cap26.log` ends `EXHAUSTED depth 46 states 1914058` with 1914057 PRIM tests and no
  goal. `rank3-cap24.log` ends `EXHAUSTED depth 37 states 280213`. That is the size of S³_24
  recorded in `ak3-aut-tunnel-closed-exhaustion`, which is a calibration of the rank-3 mode.
- `decomp.py` compares the four dumps as sets of lines, and `rank3-decomp.log` is its output.
  - The set of z-free lines of S³_C is equal, as a set of strings, to the S_C dump, for
    C = 24 and C = 26.
  - No line with z uses only two of the three generators. So every state of S³_C that is
    equivalent to a pair in F_2 appears as a z-free line.
  - Both caps satisfy S_C ⊂ S³_C, and S³_24 ⊂ S³_26.
  - The lines of S³_26 not in S³_24 split by length as stated. The z-free ones among them are
    exactly the lines of S_26 not in S_24.
- Goals on the part of length ≤ 24: S³_24 is covered by `ak3-rank3-cap24.log`, with 280213
  pairs, goals PRIM 0, THICK 0, PROJ 0, and 0 undecided. The 4036 remaining states are
  z-free.
- Goals on z-free states. Let (p, q) be z-free.
  - PRIM of (p, q) in F_3 is PRIM in F_2, because a word in F_2 is primitive in F_3 exactly
    when it is primitive in F_2.
  - The rank-3 presentation complex of (p, q) is the rank-2 one wedged with a circle. A
    thickening of the wedge restricts to a regular neighbourhood of the rank-2 complex,
    which is an orientable thickening of it. So THICK in rank 3 implies THICK in rank 2.
  - PROJ at z deletes no letter, so it is the rank-2 THICK test of (p, q).
  - PROJ at x or at y needs the exponent minor of the other generator and z to be ±1. That
    minor is 0, because z has exponent 0 in both entries.

  So on z-free states, no goal in rank 3 follows from no goal in rank 2, which is item 2.
- The 205526 new states with z had only the PRIM test of `capbfs`. So item 6 does not claim
  THICK or PROJ on them.

## Step 8: item 7 (rank 2, cap 28)

- `run.sh 2 28 33000000 c28` is the run of Step 3 at cap 28. Steps 1 and 2 apply unchanged.
- The container restarted during one slot. That slot wrote no checkpoint, and `run.sh`
  resumed from the previous checkpoint (depth 18). By Step 2 the result is that of an
  uninterrupted run. `rank2-cap28.log` marks the point with a comment line.
- The log ends `EXHAUSTED depth 68 states 11535176 processed 11535176`, with 11535175
  PRIM tests, no goal, and the length histogram of item 7.
- `cmp28.py` streams the S_28 dump against the S_26 dump. `cmp28.log` records that every
  S_26 line is an S_28 line, the length histogram of the rest, and examples. The length-19
  example of item 7 is the first line of `cmp28.log` of that length.
