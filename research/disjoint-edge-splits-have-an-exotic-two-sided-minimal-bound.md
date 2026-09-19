---
rg: 2
id: disjoint-edge-splits-have-an-exotic-two-sided-minimal-bound
kind: claim
title: In rank four two commuting edge splits have a 13-piece minimal common upper bound that is not above their square and splits two-sidedly, because a pinwheel dissection of one square piece is reachable from both sides; in rank three no such bound or exotic cell occurs in the searched range
artifacts:
  - research/artifacts/gq-bh-invent-07-edge-split-pair-bounds.md
distinct_from:
  splitting-categories-are-connected-iff-root-graphs-are: that reduces condition (G) for the edge-split operad to minimal common upper bounds of two edge splits; this shows that such bounds are not only the square and the flops, and exhibits a two-sided one of degree 13.
  edge-split-flop-spine-elements-split-disconnectedly: that computes the two-sided flop elements of degree 5 for two adjacent edge splits; this finds a two-sided element of a new type, for two disjoint (commuting) edge splits, not above their square.
  split-tree-restrictions-to-a-child-need-not-be-split-trees: that is a non-tree restriction to a child of one split; here the non-tree restriction sits in a piece of the square of two commuting splits and is reachable from both of them.
---

**ESTABLISHED** (lane bh-invent-07, 2026-09-18). The main example was found by one
coordinator-approved SLURM search (artifact). Its common-upper-bound property and its failure
to dominate the square were checked by hand below. Minimality and the list of atoms below it
are machine checks, using the exact single-removal test described in the artifact. The
negative findings are search data, not proofs. No priority is claimed.

## Notation

- Rank four: `Δ = cone(e_0, …, e_3)`. The atoms `E_01, E_23` split along `x_0 = x_1` and
  `x_2 = x_3`.
- The **square** `Sq` is `E_01` followed by `E_23` on both halves. Its four pieces are the
  regions `(±, ±)` given by the signs of `x_0 − x_1` and `x_2 − x_3`.
- Rays are written as strings, so `0111 = e_1 + e_2 + e_3`.

## Statement

1. **An exotic two-sided minimal bound.** The 13-piece dissection `Θ` below satisfies:
   - `Θ ≥_E E_01` and `Θ ≥_E E_23`;
   - `Θ ≱_E Sq`;
   - `Θ` is a minimal common upper bound of `E_01` and `E_23`;
   - the only atoms below `Θ` are `E_01` and `E_23`.

   So `Θ ∈ S_1` has a root graph with no edge, and by
   `splitting-categories-are-connected-iff-root-graphs-are` its splitting category is
   disconnected. The square and the flops are therefore not the only minimal common upper
   bounds of two edge splits.
2. **Rank three, in the searched range.**
   - Every cell of `Desc(Δ)` with entry sum ≤ 36 (BFS capped at 420,592 cells) that lies in a
     region of `E_01 ∧ E_02` and descends from both children also descends from the region cell,
     or from a flop triangle in the quad region. So there are no exotic cells.
   - All 141,103 common upper bounds of `E_01, E_02` produced by the search dominate `F_+` or
     `F_−`.

## The example

```
1  0001 0011 0111 1111     8  0010 0110 1110 1111
2  0001 0011 1000 1100     9  0010 1000 1110 1111
3  0001 0100 0111 1100    10  0100 0110 0111 1100
4  0001 0111 1100 1111    11  0110 0111 1100 1111
5  0010 0011 0111 1111    12  0110 1100 1110 1111
6  0010 0011 1000 1111    13  1000 1100 1110 1111
7  0010 0110 0111 1111
```

**Regions.** `(+,+) = {6, 9, 13}`, `(+,−) = {2}`, `(−,−) = {1, 3, 4}`, and
`(−,+) = {5, 7, 8, 10, 11, 12}`. Every piece has signs of one kind on its rays, so both
planes are respected.

**`Θ ≥_E E_01`.**
- The half `{x_0 ≥ x_1} = cone(1000, 1100, 0010, 0001)`: split at `(0010, 0001)` into
  `(+,+)` and `(+,−)`.
  - `(+,+)`: split at `(1100, 0011)`, then at `(1100, 0010)`, giving 6, 9, 13.
- The half `{x_1 ≥ x_0} = cone(1100, 0100, 0010, 0001)`: split at `(0100, 0010)` (plane
  `x_0 − x_1 + x_2 = 0`).
  - The side `cone(1100, 0100, 0110, 0001)` splits at `(0110, 0001)` into 3 and 10.
  - The side `cone(1100, 0110, 0010, 0001)` splits at `(1100, 0010)` (plane `x_1 = x_2`).
    - Pieces 4, 11, 12 come from splits at `(1110, 0001)` and `(0110, 0001)`.
    - Pieces 1, 5, 7, 8 come from `(1110, 0001)`, `(0110, 0001)` and `(0010, 0001)`.

**`Θ ≥_E E_23`.**
- The half `{x_3 ≥ x_2}`: split at `(1000, 0100)` into `(+,−) = 2` and `(−,−)`.
  - `(−,−)`: split at `(0100, 0011)` into 3 and a cell that splits at `(1100, 0011)` into 1 and 4.
- The half `{x_2 ≥ x_3} = cone(1000, 0100, 0010, 0011)`: split at `(0100, 0011)` (plane
  `x_1 = x_3`).
  - One side gives 5 and 6 via `(1000, 0111)`.
  - The other side splits at `(0100, 0010)`:
    - 7, 8, 9 come from `(1000, 0111)` and `(1000, 0110)`;
    - 10, 11, 12, 13 come from `(1000, 0100)`, `(1000, 0111)` and `(1000, 0110)`.

**`Θ ≱_E Sq`: the pinwheel.**
- The piece `(−,+) = cone(A, B, C, D)`, with `A = 1100`, `B = 0100`, `C = 0010`,
  `D = 0011`, is dissected by `{5, 7, 8, 10, 11, 12}`.
- The rays used are the four cross midpoints `A+C, A+D, B+C, B+D`.
- A split tree of that cell must respect one of its first splits. The only first splits with
  midpoints present are:
  - `(A, D)`, plane `x_0 = x_3`, straddled by piece 10;
  - `(A, C)`, straddled by 5;
  - `(B, C)`, straddled by 5;
  - `(B, D)`, plane `x_0 − x_1 + x_3 = 0`, straddled by 7.
- So `Θ|_{(−,+)}` is not a split tree, and `Θ ≱_E Sq`.

  Each side reaches this pinwheel only inside a larger tree: `E_01` through `{x_1 ≥ x_0}`,
  and `E_23` through `{x_2 ≥ x_3}`.

**Minimality and atoms (machine).**
- No single cherry removal of `Θ` is again `≥_E E_01, E_23`. By the chain argument of the
  artifact, `Θ` is minimal.
- Among the six atoms, only `E_01` and `E_23` lie below `Θ`.
- All four exotic hits of the search (common upper bounds with 14–19 pieces) minimize to
  13-piece elements with this root graph.

## What this means for condition (G)

- By `splitting-categories-are-connected-iff-root-graphs-are`, condition (G) holds for the
  edge-split operad exactly when two-sided minimal common upper bounds of two edge splits have
  **bounded degree** in each rank.
- Finitely many exotic elements are harmless. The example shows there is at least one new
  type, of degree 13, arising for commuting splits from rank 4.
- **The gate for the closed-MCG route (R1b)** is therefore now: are pinwheel-type two-sided
  minimal pair bounds finite in number, in each rank `m + 1 = 6g − 6`?
  - If yes, the edge-split group is finitely presented given Ore's condition
    (`thumann-finiteness-without-finite-type`).
  - If they have unbounded degree, Thumann's Morse method fails for the edge-split operad
    (Corollary 3 of the root-graph node). A different operad or a different complex would then
    be needed.
- In rank 3 nothing exotic was found, neither cells nor bounds. The phenomenon needs two
  commuting splits with room for a pinwheel, so it first appears in rank 4.

## Lesson for general BH

In non-LCM dissection hosts, the square of two commuting moves is not their only minimal
common refinement. A piece of the square can be dissected by a pinwheel, which is not a tree,
yet each move reaches it as part of a larger tree. That gives a second, two-sided way to
reconcile the moves.

The finiteness question for such hosts therefore concentrates on the pinwheels. Finite
presentation by Thumann's engine holds if, in each rank, there are only finitely many
"pinwheel reconciliations" of two moves. The closed-MCG edge-split host lives in rank
`6g − 6`, and that finiteness is now its precise combinatorial gate, next to Ore's condition.
