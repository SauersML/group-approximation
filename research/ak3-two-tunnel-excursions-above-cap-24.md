---
rg: 2
id: ak3-two-tunnel-excursions-above-cap-24
kind: claim
title: Excursions above length 24 with two AC products through a Whitehead-minimal point of length 25–26 enlarge the AK(3) tunnel-closed component but reach no goal; from the tunnel-only states they close after 5 rounds, at 263067 classes in rank 2 and 282352 in rank 3
distinct_from:
  ak3-aut-tunnel-closed-exhaustion: that allows one AC product per excursion above cap 24 and leaves two-product excursions open; this runs the two-product excursions whose intermediate Whitehead-minimal point has length 25–26
  one-stabilization-ac-trivial-from-thickenable-z-pair: that defines the goals and the capped search; this goes above the cap
artifacts:
  - experiments/ak3-two-tunnel-closure-2026-09-17/README.md
  - experiments/ak3-two-tunnel-closure-2026-09-17/t2m.c
  - experiments/ak3-two-tunnel-closure-2026-09-17/iter.sh
  - experiments/ak3-two-tunnel-closure-2026-09-17/loop.sh
  - experiments/ak3-two-tunnel-closure-2026-09-17/band.sh
  - experiments/ak3-two-tunnel-closure-2026-09-17/calib16.log
  - experiments/ak3-two-tunnel-closure-2026-09-17/rank2-seeded.log
  - experiments/ak3-two-tunnel-closure-2026-09-17/rank3-seeded.log
  - experiments/ak3-two-tunnel-closure-2026-09-17/band-rank2.log
---

**Proposed ESTABLISHED** by computation, through `ak3-two-tunnel-excursions-above-cap-24-proof`.
Unreviewed. This is a search negative about AK(3). It proves no triviality and no
non-triviality.

## Setting

States, moves (M1) and (M2), the goals PRIM, THICK and PROJ, tunnels, S_24 and T_24 are as in
`ak3-aut-tunnel-closed-exhaustion`. The pair AK(3) is (x³y⁻⁴, xyxy⁻¹x⁻¹y⁻¹).

- A **2-tunnel at band (24, 26]** starts at a state s of length ≤ 24.
  1. Apply one (M1) product of length > 24.
  2. Reduce greedily by Whitehead automorphisms to a minimal pair m with 24 < |m| ≤ 26.
  3. Apply any (M1) product to m, and reduce greedily again if the result is above 24.
  4. The 2-tunnel *lands* if the result has length ≤ 24. Its *endpoint* is PRIM if an entry
     has length 1.
- The **seeded closure** U_24 is the smallest set of states with these properties:
  - it contains T_24;
  - it is closed under capped moves and tunnels;
  - it is closed under 2-tunnels at band (24, 26] from every state of U_24 \ S_24.

## Claim (rank 2)

1. **U_24 is finite, with 263067 states.** These are T_24 (262642 states) plus 425 new states
   of length ≤ 24. They were added in five rounds of 224, 131, 53, 17 and 0 states.
2. **No goal.** No state of U_24 is PRIM or THICK. No tunnel or 2-tunnel from the processed
   states has a PRIM endpoint.
3. **The intermediate points are not goals.** The 2-tunnels from U_24 \ S_24 pass through 6614
   classes m of length 25 or 26. None has a primitive entry, and none is thickenable (6614
   Neuwirth tests, 0 undecided).
4. **Two AC products per excursion do reach new states at cap 24.** The first round alone
   lands 156 classes outside T_24, of lengths 22 (3), 23 (20) and 24 (133). So T_24 is not
   closed under 2-tunnels. The corollary of `ak3-aut-tunnel-closed-exhaustion` names these
   excursions as the next level, and that level is not empty at cap 24.

## Claim (rank 3)

5. **U_24 in F_3 is finite, with 282352 states.** These are T_24 (281927 states) plus 425 new
   states, added in five rounds of 224, 131, 53, 17 and 0. The rounds, the landing classes
   (156, 81, 38, 8, 0) and the 5814 NEW landing products agree exactly with rank 2.
   - In round 1 the 1714 rank-3 seeds give 8148 intermediate classes, against 4340 in rank 2.
     The extra classes land nothing that rank 2 does not.
   - In all, 10422 classes m (32.9M (M1) products) were processed.
6. **No goal.** No state of U_24 is PRIM, THICK or PROJ, and no m is either. The m classes
   took 30588 Neuwirth tests, with 0 undecided. No tunnel or 2-tunnel endpoint has an entry
   of length 1.

## What it rules out

Take a path from AK(3) to the basis pair by (M1) moves and automorphisms. Suppose each
excursion above length 24 is of one of two kinds:
- a single AC product followed by automorphisms;
- two AC products, where the second is applied at the greedy Whitehead-minimal point of the
  first and that point has length at most 26.

Suppose also that every two-product excursion starts outside S_24. Then the path stays in
U_24, which has no goal.

The step still open is the 2-tunnels that start *inside* S_24. The tunnel sweep of
`ak3-aut-tunnel-closed-exhaustion` counts about 34M in-range tunnels from S_24 (|m| = 25:
21.4M, |m| = 26: 12.6M, from `sweep2.log`). The seeded run collapses such tunnels about 14 to 1
into classes.

## Status of the band (not claimed)

Chaining three or more AC products inside the band gives k-tunnels (`band.sh`,
`band-rank2.log`). These keep landing new states, still with no goal.

- The run starts from the 14299 third-level classes of the rank-2 run.
- Three complete rounds add 124, 188 and 110 states.
- The frontier of band classes grows: 14299, then 21534, 34117 and 50829.
- The run was stopped during the fourth round.

It looks as if the Whitehead-minimal classes of length 25–26 in this component form a large
connected set. Closing it means computing the capped component at cap 26, not a closure
driven by excursions.
