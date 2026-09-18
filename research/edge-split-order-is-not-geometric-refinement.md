---
rg: 2
id: edge-split-order-is-not-geometric-refinement
kind: claim
title: An edge-split dissection can respect a first-split plane without splitting there first, because descent is not inherited by children; so edge-split order is strictly finer than geometric refinement
invalidates:
  - edge-split-dissections-respecting-an-atom-plane-split-there
  - edge-split-ore-via-atom-plane-restriction
requires:
  - edge-split-descendants-are-not-factor-closed
  - edge-splits-cut-every-rational-hyperplane
artifacts:
  - research/artifacts/gq-bh-free-54-edge-split-reversing-tests.md
distinct_from:
  edge-split-descendants-are-not-factor-closed: that shows a single descendant cell of the simplex can lie in a child without descending from it; this turns that cell into a whole edge-split dissection that respects the child's plane but is not above the child's split, which is the failure of the operad-order statement that the atom-plane route needed.
  edge-split-operad-has-common-refinements: that is Ore's condition in the operad order, which stays open and is supported by the reversing search recorded here; this only shows that Ore's condition cannot be obtained from geometric refinement.
---

**ESTABLISHED** (lane bh-free-54, 2026-09-18). Lane proof, not independently
reviewed. It uses the depth-five witness of bh-free-61. The explicit 17-piece
certificate below was checked by machine (one MSI core, seconds).

## Notation

As in `edge-split-operad-satisfies-ore` and `edge-splits-cut-every-rational-hyperplane`.
- `Trees(C)`: the edge-split dissections (split trees) of a unimodular cell `C`.
- `Desc(C)`: the iterated edge-split descendants of `C`.
- `D ≥_E D'`: `D` is obtained from `D'` by further edge splits, that is,
  `D|p ∈ Trees(p)` for every piece `p` of `D'`.
- For `m = 2` and `a = (i, j)`, `E_a` is the first split of `Δ` along the plane
  `Π_a = {x_i = x_j}`. Its children are `C_a^+ = {x_i ≥ x_j}` and `C_a^−`.

## Statement

Let `m ≥ 2`.
1. **Respecting a plane does not make it a first split.** There is
   `D ∈ Trees(Δ)` such that no piece of `D` crosses `Π_{(01)}`, yet
   `D ≱_E E_{(01)}`.
2. **Geometric refinement is not operad refinement.** In particular, `D` refines
   `E_{(01)}` geometrically without being `≥_E E_{(01)}`.

So `edge-split-dissections-respecting-an-atom-plane-split-there` (LD_atom) is
false, and the route `edge-split-ore-via-atom-plane-restriction` cannot reach its
target. Ore's condition itself is not refuted.

## Proof

Take `m = 2`; the general case follows by the block remark at the end.
- **The witness cell.** Let `e = cone((3,0,1), (2,1,1), (2,2,1))`.
  By `edge-split-descendants-are-not-factor-closed` (part 2):
  - `e ∈ Desc(Δ)`;
  - `e ⊆ C_{(01)}^+`;
  - `e ∉ Desc(C_{(01)}^+)`.
- **Why that is enough.** Suppose `D ∈ Trees(Δ)` has `e` as a piece and
  `D ≥_E E_{(01)}`. Then `D|C^+ ∈ Trees(C^+)`, so every piece of `D` inside `C^+` lies
  in `Desc(C^+)`, and in particular `e` does. That is a contradiction. So any split
  tree containing `e` is not above `E_{(01)}`.
- **A split tree containing `e` that respects `Π`.**
  - Let `D_e` consist of `e` together with the siblings of the cells along one descent
    path from `Δ` to `e`. It is a split tree with 6 pieces.
  - Resolve `Π` inside each piece of `D_e` that crosses it, using the cut lemma of
    `edge-splits-cut-every-rational-hyperplane`. That lemma produces a split tree of the
    piece whose pieces all lie on one side of `Π`.
  - The piece `e` is not touched, since it lies in `C^+`.
  - The result `D` is a split tree of `Δ` that contains `e` and respects `Π`.

  By the previous step, `D ≱_E E_{(01)}`.
- **Higher `m`.** Use the block cell with frame `K ⊕ I_{m−2}`, where `K` is the frame
  of `e`.
  - In the row-reduction test of bh-free-61, a unit row of the identity block never
    dominates a row of the `K` block, or the reverse, and two unit rows never
    dominate each other. So the only available reductions are those of the `K`
    block.
  - Hence the block cell descends from `Δ`, since `K` reduces. It does not descend
    from `C^+ = {x_0 ≥ x_1}`, since `T_{01}^{-1}K` is stuck.
  - The cut lemma holds for every `m`, so the rest of the proof is unchanged.

## Explicit certificate (`m = 2`)

The greedy resolution (split the crossed edge with the largest `|λ_a| + |λ_b|`)
gives `D` with 17 pieces. Rays are listed as integer vectors. Each line is one cone.

```
(0,0,1) (0,1,0) (1,1,1)    (0,0,1) (1,0,1) (1,1,1)    (0,1,0) (1,1,0) (3,3,1)
(0,1,0) (1,1,1) (2,2,1)    (0,1,0) (2,2,1) (3,3,1)    (1,0,0) (1,1,0) (3,2,1)
(1,0,0) (3,0,1) (3,1,1)    (1,0,0) (3,1,1) (3,2,1)    (1,0,1) (1,1,1) (2,1,1)
(1,0,1) (2,0,1) (2,1,1)    (1,1,0) (3,2,1) (3,3,1)    (1,1,1) (2,1,1) (2,2,1)
(2,0,1) (2,1,1) (3,0,1)    (2,1,1) (2,2,1) (3,0,1)    (2,2,1) (3,0,1) (3,1,1)
(2,2,1) (3,1,1) (3,2,1)    (2,2,1) (3,2,1) (3,3,1)
```

- The machine checks confirmed four things:
  - `D ∈ Trees(Δ)`;
  - `D ≥_E D_e`;
  - no piece crosses `x_0 = x_1`;
  - `D ≱_E E_{(01)}`.
- `D`'s only first split is at `(0, 2)`.
- The piece `(2,1,1) (2,2,1) (3,0,1)` is `e`.
- The exhaustive LD_atom check recorded in the refuted node reached only 7 pieces, so it
  could not see this.

## What survives

- **Ore's condition is still supported.** A reversing search (Dehornoy-style: at each
  node, reverse a pair of first splits through one of their minimal common bounds, the
  commuting square or the flop pair) found common upper bounds for:
  - `(E_{(01)}, D_e)` (27 pieces) and `(E_{(01)}, D)` (33 pieces);
  - all 320 random pairs of split trees with 3 to 16 pieces.
- **The flop and plane lemmas stand.** The atom flop relation and
  `edge-splits-resolve-every-rational-plane` are unaffected.
- **The correct reduction.** It replaces LD_atom by a synchronization part and a
  tree-domination part: `edge-split-ore-iff-synchronization-and-tree-domination`.

## Lesson for general BH

In higher-rank refinement hosts, the operad (tree) order is strictly finer than
geometric refinement.
- **The discrepancy is exactly non-inherited descent.** A cell can descend from the
  root without descending from the child that contains it.
- **Consequence for proofs.** Ore's condition cannot be read off from geometry,
  whether by cofinality of the moves or by plane-respecting refinements. It has to be
  proved in the order itself.
- **Where the distinction already exists.** Garside and Dehornoy theory draws the same
  line between left divisibility and "the element lies below". Here one can see where
  they part: a deep witness (`e` has depth five) that a small-window search never
  reaches.
- **Advice for every Stein–Farley or Thumann argument over rational polyhedral
  hosts.** Test the operad-order statements on witnesses of non-inherited descent, not
  only on small windows.
