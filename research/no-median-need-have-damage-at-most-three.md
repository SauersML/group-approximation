---
rg: 2
id: no-median-need-have-damage-at-most-three
kind: claim
title: A seventeen-piece descendant dissection of the triangle cone has, for each median, a straddling piece that the median cannot resolve in fewer than four pieces
artifacts:
  - research/artifacts/gq-bh-major-mcg-2-sc2-counterexample.md
  - research/artifacts/gq-bh-free-54-sc2-damage-tests.md
distinct_from:
  some-median-has-damage-at-most-three: that conjectured bounded damage (SC₂); this is an exact counterexample, one of 6 rank-3 and 10 rank-4 nodes found by bh-free-54's damage logging.
  no-median-need-be-single-cut-for-a-descendant-dissection: that refutes damage two (SC); this refutes damage three.
  median-cut-damage-is-born-at-parallel-splits: that proves damage above three is born only at parallel splits; this shows parallel splits can occur across all three medians in one dissection, the shape that node predicted for a counterexample.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-19). An explicit finite example, found by
bh-free-54 (`sc2_damage.py`, landed at acb6bede1) and re-checked here with independent
exact code. Damage is computed here as the least number of pieces, not by one resolution
rule. No priority claimed.

## Statement

The 17 cells below, given by their rays, form a descendant dissection `D` of
`Δ = cone(e_0, e_1, e_2)`:
- every piece is unimodular and lies in `Desc(Δ)`;
- the pieces are pairwise interior-disjoint;
- the weights sum to `1`.

```
(0,0,1) (0,1,2) (1,0,2)    (0,1,0) (7,0,3) (12,0,5)    (0,1,1) (1,3,3) (2,0,1)
(0,1,0) (0,2,1) (1,1,1)    (0,1,1) (0,1,2) (1,0,2)    (1,0,0) (3,0,1) (3,1,1)
(0,1,0) (1,0,0) (3,1,1)    (0,1,1) (0,2,1) (1,1,1)    (1,1,1) (1,2,2) (2,0,1)
(0,1,0) (1,1,1) (2,0,1)    (0,1,1) (1,0,1) (1,0,2)    (1,2,2) (1,3,3) (2,0,1)
(0,1,0) (2,0,1) (7,0,3)    (0,1,1) (1,0,1) (2,0,1)    (5,0,2) (12,0,5) (12,1,5)
(0,1,0) (3,0,1) (5,0,2)
(0,1,0) (5,0,2) (12,1,5)
```

For each median, some straddler has damage at least `4`:

| median | form | straddler | values | least damage |
|---|---|---|---|---|
| `x_1 = x_2` | `x_2 − x_1` | `(0,1,0) (3,0,1) (5,0,2)` | `−1, 1, 2` | 4 |
| `x_0 = x_2` | `x_0 − x_2` | `(0,1,1) (1,3,3) (2,0,1)` | `−1, −2, 1` | 4 |
| `x_0 = x_1` | `x_1 − x_0` | `(0,1,0) (1,0,0) (3,1,1)` | `1, −1, −2` | 4 |

None of these value vectors lies in the damage-3 classes `±(1,1,−1)`, `±(2,−1,0)` of
`median-cut-damage-is-born-at-parallel-splits`, which gives damage `≥ 4` by hand. The
exact search gives exactly `4`. So SC₂ (`some-median-has-damage-at-most-three`) is false.

## Context (bh-free-54's run)

- **Frequency.** Among the nodes of the least-damage recursion, SC₂ fails at 6 of 18018
  in rank 3 and at 10 of 36670 in rank 4.
- **Tree domination is unaffected.** The recursion still terminated on all 336 rank-3
  non-tree instances, and on 1412 of 1416 in rank 4 (the 4 caps were inside
  subroutines).
- **The three saved rank-3 nodes** (17, 60 and 230 pieces) all re-check exactly. This
  one is the smallest.

## Reading

- **The predicted shape.** Every heavy straddler here descends through a parallel split,
  as `median-cut-damage-is-born-at-parallel-splits` requires. The counterexample has
  parallel-split families across all three medians at once: the obstruction shape that
  node named.
- **The pattern repeats.** Values `(−1, 1, 2)` and `(1, −1, −2)` are the far-edge pattern
  `(1, −1, 2)` of the five-piece tree there.
- **No fixed local bound holds.** SC (damage 2) and SC₂ (damage 3) both fail at a small
  fraction of nodes. The failure rate falls with the bound, from 148 per 14086 to
  6 per 18018. So a fixed per-node damage bound is not the invariant.

## Lesson for general BH

- **Per-node bounds fail; the potential must be global.** For tree domination in
  non-LCM dissection operads, every per-node invariant tested (rearrangement, single
  cuts, bounded damage) fails at a small, shrinking fraction of nodes, while the
  recursion itself always terminates. A proof needs a potential that pays for the rare
  heavy nodes out of earlier savings. It cannot be a bound that holds at every node.
- **Candidate currency.** Parallel splits are where damage is born, so they are the
  natural currency for such an amortized potential.
