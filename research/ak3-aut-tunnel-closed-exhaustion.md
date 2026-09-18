---
rg: 2
id: ak3-aut-tunnel-closed-exhaustion
kind: claim
title: The AK(3) relator-pair component stays finite and goal-free when single AC products of any length followed by Whitehead reduction ("tunnels") are allowed; in rank 2 at cap 24 it has 262642 classes, so a path to the basis pair needs an excursion above length 24 with two AC products or one that starts with an automorphism
distinct_from:
  one-stabilization-ac-trivial-from-thickenable-z-pair: that defines the goals and records the capped search, in which every intermediate state has total length at most the cap; this lets one AC product per excursion go to any length and still exhausts the component
  thickenable-z-pairs-lie-in-the-move-class-of-a-basis-pair: that shows the thickenable and primitive goals have the same reach, so a meeting can only happen above cap 24; this rules out the cheapest paths above cap 24, those whose excursions contain a single AC product
artifacts:
  - experiments/ak3-aut-tunnel-closure-2026-09-17/README.md
  - experiments/ak3-aut-tunnel-closure-2026-09-17/tunnel.c
  - experiments/ak3-aut-tunnel-closure-2026-09-17/grow.c
  - experiments/ak3-aut-tunnel-closure-2026-09-17/sweep2.log
  - experiments/ak3-aut-tunnel-closure-2026-09-17/grow2.log
  - experiments/ak3-aut-tunnel-closure-2026-09-17/growcaps.log
---

**Proposed ESTABLISHED** by computation, through `ak3-aut-tunnel-closed-exhaustion-proof`.
Unreviewed. It is a search negative about AK(3): it proves no triviality.

## Setting

AK(3) is the pair (x³y⁻⁴, xyxy⁻¹x⁻¹y⁻¹). The states, moves and goals are those of
`experiments/ak3-thick-z-pair-search-2026-09-17/thzsearch.c`. In rank R ∈ {2, 3}:

- A **state** is a pair of cyclic words in F_R, up to swapping the entries and permuting
  and inverting generators. Its length is the total length.
- **(M2)** applies one Whitehead automorphism of the second kind to both entries. All of
  them are used (12 in rank 2, 90 in rank 3), and the set is closed under inverses.
- **(M1)** replaces u by a cyclic reduction of u′ g v′^{±1} g⁻¹, where u′, v′ are rotations of
  u and of the other entry v, and g is empty or one letter.
- **Goals.** PRIM means an entry is primitive; THICK means the pair is orientably thickenable
  (Neuwirth test `thick2.c`); PROJ, in rank 3, is a thickenable projection.
- **Capped moves at cap C.** Moves whose result has length at most C.
- **Tunnel at cap C.** One (M1) move whose result has length > C, followed by greedy
  Whitehead reduction to a Whitehead-minimal pair m. It lands on m if |m| ≤ C. Its
  endpoint is PRIM if an entry of m has length 1.

The **tunnel-closed component** T_C is the smallest set of states containing AK(3) that is
closed under capped moves and tunnels at cap C. The capped component S_C ⊂ T_C is the one
searched in `one-stabilization-ac-trivial-from-thickenable-z-pair`.

## Claim

1. **Rank 2, cap 24.** T_24 is finite, with 262642 states. It consists of S_24 (261720
   states) and 922 more states of length 21–24. No state of T_24 is PRIM or THICK, and no
   tunnel from T_24 has a PRIM endpoint. In all, 534,603,117 tunnels were tested:
   532,381,654 from S_24 and 2,221,463 from the new states.
2. **Smaller caps.** T_C is exhausted with no goal, no THICK state and no PRIM tunnel
   endpoint for these caps:

   | cap C | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 |
   |---|---|---|---|---|---|---|---|---|
   | rank 2, \|T_C\| | 69 | 150 | 616 | 1144 | 3903 | 6955 | 23515 | 41531 |
   | rank 2, \|S_C\| | | 146 | | 1110 | | 6867 | | 41257 |
   | rank 3, \|T_C\| | 69 | 150 | 616 | 1144 | 3906 | 6963 | 23785 | |

   At caps 13 and 14, T_C = S_C = {AK(3)}.
3. **Rank 3, cap 24.** Pending; see Attempts. S_24 has 280213 states, and a one-step
   tunnel sweep over it is running.

## Consequence for paths

Consider a path of states from AK(3) to the basis pair (x, y), by moves (M1) and
arbitrary automorphisms of F_2. An **excursion** is a maximal stretch of the path above
length 24; since both ends have length at most 24, every excursion starts and ends at
states of length at most 24.

**Corollary.** Some excursion either contains at least two (M1) moves, or begins with an
automorphism and contains an (M1) move.

The endpoint of an excursion made of one (M1) move followed by automorphisms lies in T_24
(Step 3 of the proof, by Whitehead peak reduction). So does the endpoint of an excursion
made of automorphisms only. Below the cap, an automorphism between two states of length at
most 24 factors into capped (M2) moves, by peak reduction again. So a path without such an
excursion stays in T_24, and T_24 does not contain (x, y). The cheapest paths that leave
the capped graph are ruled out. A bidirectional search above cap 24 has to allow at least
two AC products per excursion.

## Rank-2 structure found on the way

- **Tunnels are needed to close the component.** S_24 is closed under capped (M1) moves
  (0 closure violations over 19,260,026 capped products). The 649 new tunnel endpoints are nevertheless
  not in S_24.
- **The capped move graph is not symmetric.** From one such endpoint,
  (x⁴y³, x⁴y⁶x⁻¹y⁻¹xy⁻¹x⁻¹y⁻²), the capped search reaches all of S_24 (261722 states: S_24
  plus two). S_24 does not reach it. The (M1) moves as generated are not closed under
  inverses.
- **Length of endpoints.** The Whitehead-minimal endpoints of all tunnels from S_24 have
  length 13 to 45 (histogram in `sweep2.log`). The 2194 new ones within cap 24 have length
  21 (2), 22 (13), 23 (358) and 24 (1821). They fall into 649 classes.
