# AK(3): tunnel-closed components (lane w6-082, 2026-09-17)

This lane tests the shared assumption of the length-capped searches that every intermediate
state of a trivializing path is short. A **tunnel** is one AC product (M1) of any length.
It is followed by greedy Whitehead reduction to a Whitehead-minimal pair m, and kept if
|m| ≤ CAP. Every tunnel is a composition of moves (P1) and (P2).

## Files

- `tunnel.c` loads a component dump from `thzsearch.c` and applies every (M1) product to
  each state. Products of length ≤ CAP are checked for closure violations. Longer products
  are tunnelled, then flagged as follows:
  - PRIM, if a Whitehead-minimal endpoint has an entry of length 1;
  - NEW, if the endpoint has length ≤ CAP and is not in the dump;
  - thickenable, if the endpoint has length ≤ TCAP, after the planarity prefilter.
- `tbfs.c` runs a BFS of the tunnel-closed component: capped (M2), capped (M1), then
  tunnels. The option `notun` reproduces `thzsearch.c` exactly: 6875 states at cap 20 in
  rank 3.
- `runcaps.sh` runs `tbfs` over a list of caps, under `nice -n 10 timeout 1200`.
- `grow.c` loads a known component as visited, inserts seed states, and runs a BFS over
  the new states only, with capped (M2), capped (M1) and tunnels. Every new state gets the
  full goal test. It writes the new states. From AK(3) alone it computes T_C from scratch
  and reproduces `tbfs`: 6955, 23515 and 41531 states at caps 20–22 in rank 2, with the
  same tunnel count at cap 22.
- `sweep.sh` runs `tunnel` over a dump in chunks, one tunnel step from every state, and
  keeps the new endpoints. `canon.c` prints canonical forms: `./canon RANK < pairs`.
- `growcaps.sh` runs `grow` from AK(3) over a list of caps.
- `newcanon.txt` holds the 649 canonical new endpoints of the rank-2 cap-24 sweep.

Both tools `#include "thzsearch.c"` and link its `thick2.c`, from
`experiments/ak3-thick-z-pair-search-2026-09-17/`. Build:

    gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o tbfs tbfs.c
    gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o tunnel tunnel.c
    gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o grow grow.c
    gcc -O2 -I ../ak3-thick-z-pair-search-2026-09-17 -o canon canon.c

## Built-in checks

- **Cut formula.** Greedy reduction uses |φ(w)| − |w| = cap(A) − deg(a) on the Whitehead
  graph, and each step asserts it against direct application. The `selftest` mode compared
  17.8M Whitehead-automorphism applications in ranks 2 and 3 with 0 mismatches.
- **Planarity prefilter.** A thickenable one-vertex complex has a planar link, i.e. a
  planar Whitehead graph. The prefilter rejects graphs containing K5, K5 with one edge
  subdivided, or K3,3 on the 6 vertices. It rejects 697 of the 32768 labelled simple
  graphs on 6 vertices, which is the count of non-planar ones.
- **Calibration on AK(2) = (xxYYY, xyxYXY).**
  - In rank 2 at cap 11, the capped component has 1 state. Tunnels from it give 22 NEW
    states of length 10, and `tbfs` reaches PRIM within 3 steps.
  - In rank 3 at cap 13, PRIM is found at a tunnel endpoint after 1 step. With `noprim`,
    THICK is reached at depth 2.

## Results

Node: `research/ak3-aut-tunnel-closed-exhaustion.md`.

- **Rank 2, cap 24.** T_24 = S_24 ∪ 922 new states, 262642 in all.
  - `sweep2.log`: one tunnel step from all 261720 states of S_24. There were 532,381,654
    tunnels and 19,260,026 capped products, with 0 closure violations and 0 endpoints with
    an entry of length 1. It found 16383 new endpoints, which are 649 classes.
  - `grow2.log`: growth from those 649 classes ends EXHAUSTED with 922 new states,
    2,221,463 tunnels, and goals PRIM 0, THICK 0 (0 undecided).
- **Rank 3, cap 24.** T_24 = S_24 ∪ 1714 new states, 281927 in all.
  - `sweep3.log`: one tunnel step from all 280213 states. The timed-out chunk
    240000–270000 was rerun in halves by `resweep.sh`. There were 805,596,332 tunnels and
    20,159,284 capped products, with 0 violations and 0 PRIM endpoints. The new endpoints
    fall into 1397 classes (`newcanon3.txt`).
  - `grow3.log`: growth from those classes ends EXHAUSTED with 1714 new states, 5,284,987
    tunnels, and goals PRIM 0, THICK 0, PROJ 0 (0 undecided).
- **Caps 13–23.** `tr2.log` and `tr3.log` (tbfs), and `growcaps.log` (grow from scratch)
  are all EXHAUSTED with no goal, except rank 3 at cap 23, which hit the time limit.
- **2-tunnels.** `grow2t.c` adds a second (M1) product from each reduced tunnel endpoint of
  length at most C2. Build it like `grow`; usage is `grow2t RANK CAP C2 base seeds out`.
  `grow2t.log` records the runs:
  - With C2 = CAP it reproduces `grow`.
  - For AK(3) at cap 16, with C2 = 24 or 30, it gives 161 states (against 150 with tunnels
    only), with no goal.
- **Asymmetry.** `thzsearch 2 24 20000000 XXXXYYY XXXXYYYYYYxyXyxyy dump` gives 261722
  states, which contain all of S_24. So a new endpoint reaches S_24 by capped moves, while
  S_24 does not reach it.

Reproduce S_24 with `thzsearch 2 24 20000000 xxxYYYY xyxYXY dump` (THZ_DUMP=s24r2.txt).
Then run `sweep.sh 2 s24r2.txt 261720 40000`, and canonicalize the `sw_*.new` files with
`canon`. Finally run `grow 2 24 s24r2.txt newcanon.txt out`. Each step is single-threaded,
and each chunk takes under 200 s.
