# AK(3): 2-tunnels above cap 24 (lane w7-082, 2026-09-18)

This continues `experiments/ak3-aut-tunnel-closure-2026-09-17/` (lane w6-082). That lane
computed the tunnel-closed component T_24 of AK(3) = (xxxYYYY, xyxYXY): capped moves at total
length ≤ 24 plus *tunnels* (one AC product (M1) of any length, then greedy Whitehead reduction
back to length ≤ 24). It found T_24 = S_24 ∪ 922 states in rank 2 and S_24 ∪ 1714 in rank 3,
with no goal. The corollary left open the excursions above 24 carrying two AC products.

A **2-tunnel** is: an (M1) product above cap 24, greedy Whitehead reduction to a minimal pair
m with 24 < |m| ≤ C2, then any (M1) product from m and greedy reduction again. It lands if the
result has length ≤ 24. Here C2 = 26. A **k-tunnel in the band** chains k such steps, each
intermediate Whitehead-minimal point having length in (24, C2].

## The tool: `t2m.c`

The w6 tool `grow2t.c` redoes the second level from every tunnel. `t2m.c` factors it through the
set M of intermediate classes m (up to swapping entries and signed permutations). The second
level depends only on the class of m, and the classes repeat heavily: 61712 in-range tunnels
from the 922 seeds give 4340 classes.

- `t2m A RANK 24 C2 base[,base2] lo hi out` writes the classes m (24 < |m| ≤ C2) reached by
  one tunnel from states lo..hi−1 of the base.
- `t2m B RANK 24 C2 base[,base2] mlist lo hi out` takes entries lo..hi−1 of mlist and does two
  things for each m.
  - It tests the goals on m itself: PRIM by `is_primitive`; THICK by `thick2` after the
    planarity prefilter; PROJ in rank 3.
  - It then applies every (M1) product. A product of length ≤ 24 is reported as NEW if it is
    not in the base. A longer one is reduced. The result is PRIM if an entry has length 1,
    and NEW if its length is ≤ 24 and it is not in the base. If its length is in (24, C2] and
    it is not in mlist, it goes to `out`: that is the next level.
- Membership in the base does not depend on which minimal representative the greedy
  reduction picks. Whitehead-minimal representatives of one Aut-orbit are joined by
  length-preserving Whitehead moves, and T_24 is closed under capped (M2).

Build it next to the w6 and thick-search sources:

    gcc -O2 -I ../ak3-aut-tunnel-closure-2026-09-17 -I ../ak3-thick-z-pair-search-2026-09-17 -o t2m t2m.c

The drivers are:

- `iter.sh` runs one round: mode A on the states added in the last round, then mode B on the
  new classes in chunks, then `canon`, then `grow` from the landings (capped moves and tunnels).
- `loop.sh` runs rounds until one adds no state.
- `band.sh` also processes the next-level classes, which gives k-tunnels in the band.

Every run is `nice -n 10 timeout 1200`, single-threaded, and every chunk must exit 0.

## Calibration (`calib16.log`)

This is AK(3) in rank 2 at cap 16 with C2 = 24, the configuration where `grow2t` gives
161 states against 150 with tunnels only.

- Mode A on T_16 gives 16575 classes, and mode B on them lands 7 new classes.
- `grow` turns these into 11 new states, and a second mode-B pass adds nothing.
- The closure has 161 states with no goal, matching `grow2t`.

## Results

See `research/ak3-two-tunnel-excursions-above-cap-24.md`.

- `rank2-seeded.log` covers rank 2 at C2 = 26, with 2-tunnels applied from every state
  outside S_24 (the 922 seeds and everything grown from them).
  - It takes five rounds. The rounds add 224, 131, 53, 17 and 0 states, 425 in all.
  - In all, 6614 m classes were processed (lengths 25 and 26), with 15,380,180 (M1)
    products from them.
  - No goal was found in any grown state, no m is PRIM or THICK, and no endpoint has an
    entry of length 1.
  - The closure has 263067 states.
- `rank3-seeded.log` covers rank 3 at C2 = 26 (`CHUNK=800 loop.sh 3 26 s24r3.txt empty.txt
  new1714r3.txt r3r 1`, 16 mode-B chunks, all exit 0).
  - The five rounds add 224, 131, 53, 17 and 0 states, exactly as in rank 2. The landings
    (5814 products, 156/81/38/8/0 classes) are the rank-2 ones.
  - Round 1 has 8148 classes against 4340 in rank 2, and 10422 in all. That is 32.9M (M1)
    products.
  - No PRIM, THICK or PROJ goal was found: 30588 Neuwirth calls, 0 undecided.
  - The closure has 282352 states.
- `band-rank2.log` covers k-tunnels in the band (24, 26] in rank 2, starting from the 14299
  next-level classes.
  - Three complete rounds add 124, 188 and 110 states, with no goal.
  - The frontier grows (21534, 34117, 50829), and the run was stopped during round 4.
