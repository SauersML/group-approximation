---
rg: 2
id: ak3-rank2-capped-component-at-total-length-26
kind: claim
title: The capped AC component of AK(3) at total length 26 in rank 2 is finite, with 1690039 classes, none primitive or thickenable; its part of length at most 24 has 4036 classes more than S_24, the shortest of length 19; in rank 3 the component has 1914058 classes and no primitive, and its z-free part is exactly the rank-2 component; at cap 28 the rank-2 component has 11535176 classes, none primitive
distinct_from:
  one-stabilization-ac-trivial-from-thickenable-z-pair: that records the capped components S_C for C at most 24; this exhausts S_26
  ak3-two-tunnel-excursions-above-cap-24: that closes S_24 under excursions of one or two AC products above 24 through a Whitehead-minimal point; this allows every chain of capped moves inside total length 26, which is what that node's band section says is needed to close the band
artifacts:
  - experiments/ak3-cap26-component-2026-09-17/README.md
  - experiments/ak3-cap26-component-2026-09-17/capbfs.c
  - experiments/ak3-cap26-component-2026-09-17/thkcheck.c
  - experiments/ak3-cap26-component-2026-09-17/run.sh
  - experiments/ak3-cap26-component-2026-09-17/thkrun.sh
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

**Proposed ESTABLISHED** by computation, through
`ak3-rank2-capped-component-at-total-length-26-proof`. Unreviewed. This is a search negative
about AK(3). It proves no triviality and no non-triviality.

## Setting

States, the moves (M1) and (M2), the goals PRIM and THICK, and the capped component S_C are
as in `ak3-aut-tunnel-closed-exhaustion`, in rank 2. The pair AK(3) is
(x³y⁻⁴, xyxy⁻¹x⁻¹y⁻¹).

- A state is a pair of cyclic words in F_2 = ⟨x, y⟩, up to swapping the entries and
  permuting and inverting generators. Its length is the total length.
- S_C is the connected component of AK(3) in the graph of states of length ≤ C, with edges
  the moves (M1) and (M2) whose result has length ≤ C.
- The earlier record is S_24, with 261720 states and no goal
  (`one-stabilization-ac-trivial-from-thickenable-z-pair`, Attempt 6 of
  `andrews-curtis-conjecture`).

## Claim

1. **S_26 is finite, with 1690039 states.** Breadth-first search from AK(3) is exhausted
   after 46 levels. By total length:

   | length | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
   | S_26 | 2 | 5 | 72 | 83 | 476 | 541 | 2910 | 3169 | 17268 | 18775 | 102841 | 119614 | 637882 | 786401 |
   | S_24 | 2 | 5 | 72 | 83 | 476 | 541 | 2905 | 3159 | 17189 | 18658 | 101800 | 116830 | | |

2. **No goal.** No state of S_26 has a primitive entry (1690038 tests; the start is AK(3)).
   No state is orientably thickenable: the 1428319 states outside S_24 took 1428319
   Neuwirth tests with 0 undecided, and S_24 was tested before.
3. **No short state.** The minimum length in S_26 is 13. It is attained by two states,
   (x⁻¹y⁻¹x⁻¹yxy, x⁻⁴y³), which is AK(3) itself, and (x⁻²y⁻¹xy², x⁻³y²xy⁻¹). So S_26 has no
   state of length ≤ 12. Any such state would be AC-trivial by
   `short-balanced-trivial-presentations-are-trivial-or-ak3`.
4. **Raising the cap from 24 to 26 changes the part of length ≤ 24.** S_24 ⊂ S_26, and the
   part of S_26 of length ≤ 24 has 265756 states. The 4036 states not in S_24 have lengths
   19 (5), 20 (10), 21 (79), 22 (117), 23 (1041) and 24 (2784). Three of the five of length
   19 are
   - (x⁻³y⁻¹x²y², x⁻²y⁻¹x⁻¹yxy⁻¹xyxy),
   - (x⁻³y⁻¹x⁻¹y⁻¹x²y, x⁻²y⁻²xyxy⁻¹x⁻¹y), and
   - (x⁻²y⁻¹x²y², x⁻¹y⁻¹x⁻¹yxy⁻³x⁻¹yxy⁻¹).

   Each lies at total length 19 but is joined to AK(3) only through states of length 25 or 26.
5. **The Alexander polynomials of the one-relator quotients are not an obstruction.** For a
   state (r_1, r_2), each G_i = ⟨x, y | r_i⟩ has abelianization Z and an Alexander polynomial
   Δ_i. At AK(3) they are those of the (3,4) torus knot and the trefoil. Over S_24:
   - 4395 states have Δ_1 = 1 or Δ_2 = 1;
   - 17 states have Δ_1 = Δ_2 = 1, for example (x⁻²y⁻¹xy⁻¹x⁻¹yxyxy, x⁻²y⁻¹xy⁻¹x⁻¹y²x²y⁻¹x⁻¹y).

   So the pair (Δ_1, Δ_2) already takes, inside S_24, the value (1, 1) it has at the basis
   pair. Take any function of the unordered pair {Δ_1, Δ_2} that is unchanged by the moves
   (M1) and (M2). It takes the same value at AK(3) and at the basis pair, so it cannot
   separate them.
6. **Rank 3.** Let S³_C be the capped component of AK(3) in rank 3, with the same moves and
   the goals PRIM, THICK and PROJ of `ak3-aut-tunnel-closed-exhaustion`. Call a state
   z-free if neither entry uses the third generator z, up to the symmetries.
   - S³_26 is finite, with 1914058 states. Breadth-first search is exhausted after 46
     levels, and no state has a primitive entry (1914057 tests).
   - The z-free states of S³_26 are exactly the 1690039 states of S_26, and the z-free states
     of S³_24 are exactly the 261720 states of S_24. So at both caps, passing through states
     that use z joins AK(3) to no pair in F_2 that the rank-2 moves do not already reach.
   - S³_24 ⊂ S³_26. The 1633845 states of S³_26 not in S³_24 are the 1428319 states of
     S_26 not in S_24, plus 205526 states that use z. Every one of those 205526 has length
     25 (83519) or 26 (122007).
   - So the part of S³_26 of length ≤ 24 is S³_24 together with the 4036 z-free states of
     item 4. All 280213 states of S³_24 were goal-tested before, with no goal
     (`ak3-rank3-cap24.log` of `experiments/ak3-thick-z-pair-search-2026-09-17`). The z-free
     states of S³_26 are the pairs of S_26, tested by item 2.
   - The 205526 new states that use z were tested for PRIM only. THICK and PROJ were not run
     on them.

   By total length, S³_26 is 13:2 14:5 15:72 16:83 17:476 18:541 19:2913 20:3174 21:17530
   22:19409 23:109617 24:130427 25:721401 26:908408 (`rank3-cap26.log`).
7. **Rank 2, cap 28 (PRIM only).** S_28 is finite, with 11535176 states. Breadth-first
   search is exhausted after 68 levels, and no state has a primitive entry (11535175
   tests). The minimum length is still 13. By length it is 13:2 14:5 15:72 16:83 17:476
   18:541 19:2911 20:3180 21:17339 22:18954 23:103537 24:120917 25:645260 26:809954
   27:4188175 28:5623770 (`rank2-cap28.log`).
   - S_26 ⊂ S_28. Raising the cap again adds short states: 2261 of length ≤ 24 and 30931 of
     length 25 or 26 (`cmp28.log`). The shortest is (x⁻³y⁻¹x²y³, x⁻²y⁻¹xyx⁻¹y⁻¹xy²), of
     length 19.
   - THICK was not run on S_28.

## What it rules out

Consider a path from AK(3) to a primitive or thickenable pair by moves (M1) and (M2), in
rank 2. Every such path passes through a state of total length at least 27. Before this
node the bound was 25. For a path to a primitive pair, item 7 raises the bound to 29. In rank 3, every path from AK(3) to a primitive pair passes through
total length at least 27, where the previous record was cap 24
(`ak3-rank3-caps21-26.log`, where cap 25 timed out). The same holds for a path to a THICK or
PROJ goal, unless that path passes through one of the 205526 untested states.

Item 6 also bounds what the third generator can do at these caps. Within capped moves, the
detours through z only lengthen paths between pairs in F_2 that are already joined in rank 2.
They never reach a new pair in F_2.

Item 4 shows that a capped component is not a stable picture of the lengths below its cap.
S_24 misses states of length 19 that are joined to AK(3) through length 26.

## Not claimed

- The part of S_26 of length ≤ 24 (265756 states) and V_24 of
  `ak3-two-tunnel-excursions-above-cap-24` (264877 states) were not compared. Neither
  inclusion is claimed.
- THICK on S_28 minus S_26 (9844054 states) is not claimed.
- THICK and PROJ on the 205526 states of S³_26 that use z and lie outside S³_24 are not
  claimed.
- The equality of z-free parts in item 6 is claimed only at caps 24 and 26. It is not claimed
  for all caps.
