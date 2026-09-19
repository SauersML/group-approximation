---
rg: 2
id: median-cut-damage-is-born-at-parallel-splits
kind: claim
title: A median needs more than three pieces to resolve a descendant only if some ancestor needing exactly three was split along an edge the median does not cross; being clean at the centroid does not prevent this
artifacts:
  - research/artifacts/gq-bh-major-mcg-2-damage-lemma.md
distinct_from:
  mid-median-bad-cuts-need-a-badly-cut-creating-ancestor: that traces a bad cut at a vertex on the median to the ancestor that created the vertex; this traces damage above three, including pieces with no vertex on the median, to one split in the descent path.
  no-median-need-be-single-cut-for-a-descendant-dissection: that refutes zero damage (SC) and asks for damage at most three (SC₂); this gives the exact classes of small damage and the one mechanism that creates larger damage.
  some-median-is-single-cut-at-the-centroid: that finds a median clean at the centroid; this shows such a median can still have damage four elsewhere, so it is not the median SC₂ needs.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-19). A lane proof, elementary and not
independently reviewed. The finite tables are checked by exact search (artifact). No
priority claimed.

## Setting

- `m = 2`. `g` is a cell and `M = ker ℓ` is one of its medians.
- The *values* of a cell `r` are `ℓ` on its three rays, a primitive integer vector.
  - In `g`'s coordinates, if `X` is the frame of `r` with rays as columns and
    `ℓ = y_i − y_j`, the values are `row_i(X) − row_j(X)`.
  - `r` *straddles* `M` exactly when those two rows are incomparable.
- Splitting `r` at slots `(a, b)` gives children with `v_b ↦ v_a + v_b` and with
  `v_a ↦ v_a + v_b`. The edge is *crossed* if `v_a v_b < 0`.
- The *damage* `δ(r)` is the least number of pieces of a split tree of `r` that
  respects `M`. It is `1` when `r` does not straddle `M`.

## Statement

1. **Classes of small damage.** Up to sign and permutation of the values:
   - `δ = 2` exactly for `(1, −1, 0)`: the single-cut pieces;
   - `δ = 3` exactly for `(1, 1, −1)`, the *double-midpoint* pieces, and for
     `(2, −1, 0)`, the *off-by-one* pieces through a vertex.
2. **The only way damage above three is born.**
   - **Hypothesis.** Let `r ∈ Desc(g)` straddle `M` with `δ(r) ≥ 4`.
   - **Conclusion.** On any descent path from `g` to `r`, the first ancestor `A′` with
     `δ ≥ 4` is a child of an ancestor `A` with `δ(A) = 3`, split along an edge of `A`
     that `M` does not cross. More precisely, one of the following holds:
     - `A` is double-midpoint, split at the edge joining its two rays on the same side
       of `M`;
     - `A` is off-by-one, split at an edge through its ray on `M`, and `A′` is the child
       that replaces that ray.
   - **Single-cut pieces are safe.** They never have a child of damage `≥ 4`.
   - **Crossed splits are safe.** A split along a crossed edge never raises the damage
     above `3`, starting from damage `≤ 3`.
3. **Cleanness at the centroid is not enough.** Take the five-piece split tree of `Δ`
   obtained as follows:
   - split at `(e_0, e_2)`;
   - split the half `K = cone(e_0, e_1, v_{02})` at its far edge `(e_0, v_{02})`;
   - split `cone(u, e_1, v_{02})` at `c`, with `u = (2,0,1)`;
   - then split `cone(u, e_1, c)` at `(2,1,1)`.

   Its median `x_0 = x_1` is single-cut at every piece containing `c`. But it crosses
   `cone(e_0, e_1, u)` with values `(1, −1, 2)`, so its damage is `4`.

## Proof

1. **Classification.**
   - `δ = 2` means one split respects `M`. By part 1 of
     `single-cut-is-a-mediant-condition-along-the-median`, that forces the values
     `(s, −s, 0)`, and primitivity gives `s = 1`.
   - `δ = 3` means some first split has one clean child and one single-cut child.
     Write the values as `(p, q, r)` and split at slots `(0, 1)`; by symmetry, let the
     child `(p + q, q, r)` be single-cut. Then:
     - `p + q = 0` and `r = −q` give `(−q, q, −q)`;
     - `r = 0` and `p + q = −q` give `(−2q, q, 0)`;
     - `q = 0` makes the piece itself single-cut.

     In the first two cases the other child is clean, and primitivity forces `q = ±1`.
   - The exhaustive search of the artifact agrees, over all primitive straddling vectors
     with entries in `[−5, 5]`.
2. **Birth.**
   - Ancestors of a straddler straddle, and `g` has values `(1, −1, 0)`, so `δ(g) = 2`.
     The first ancestor of damage `≥ 4` therefore has a parent of damage `2` or `3`.
   - The children of the three class representatives under every split are in the
     artifact:
     - `(1, −1, 0)`: every child has `δ ≤ 3`;
     - `(1, −1, 1)`: only the split at slots `(0, 2)`, the uncrossed edge, gives
       children of damage `4`;
     - `(2, −1, 0)`: only the children replacing slot `2`, the ray on `M`, have damage
       `≥ 4`. They are `(2, −1, 2)` and `(2, −1, −1)`.
   - Sign changes and permutations of slots commute with the split rule, so the table
     covers every member of each class.
3. **The example.** The artifact lists the values of all five pieces for the three
   medians.
   - The pieces containing `c` are `cone(v_{02}, e_1, e_2)` and `cone(w, e_1, c)`, both
     with values `(1, −1, 0)`, and `cone(u, c, v_{02})`, `cone(u, w, c)`, which do not
     straddle.
   - `cone(e_0, e_1, u)` has values `(1, −1, 2)`, which lies in neither class of
     part 1.
   - Its parent `K` is double-midpoint, split at its uncrossed far edge, as part 2
     requires.
   - The tree's root median `x_0 = x_2` has no straddler, so SC₂ holds for this tree
     through another median. ∎

## What this says about SC₂

- **The birth certificate.** A median has damage `≤ 3` for a descendant dissection `D`
  unless some piece of `D` descends, and stays heavy, through a *parallel split*. That
  is a split of a double-midpoint or off-by-one ancestor along an edge the median does
  not cross.
- **Where parallel splits come from.** The far-edge split of LD_atom is the basic
  example; it produced every earlier counterexample of this line.
- **Choosing the median.** The pattern in the three logged `no_sc` nodes, where the
  heavy median was exactly the one bad at the centroid, is not a theorem. Part 3 shows
  a median clean at `c` with damage `4`. So SC₂ cannot be proved by choosing the median
  locally at `c`. A proof must choose globally, for instance a median along which no
  piece has a parallel-split ancestor.

## Lesson for general BH

- **Damage has a birth certificate.** In non-LCM dissection operads, a generator cut
  that crosses a piece badly always goes back to one earlier split taken *parallel* to
  the cut, in an ancestor the cut already crossed mildly.
- **Consequence.** Bounded-damage invariants (SC₂-type potentials for tree domination)
  are statements about where parallel splits can occur.
- **They are global.** Cleanness at the point where all cuts meet does not control
  them, because the far-edge split is a parallel split that leaves that point clean.
