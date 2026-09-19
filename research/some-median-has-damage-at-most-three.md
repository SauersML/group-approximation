---
rg: 2
id: some-median-has-damage-at-most-three
kind: claim
title: Every descendant dissection of a rank-three unimodular cell has a median that resolves each straddling piece in at most three pieces
refuted_by:
  - no-median-need-have-damage-at-most-three
distinct_from:
  edge-split-descendant-dissections-have-single-cut-first-splits: that asked for damage two (SC) and is refuted; this asks for damage at most three (SC₂).
  median-cut-damage-is-born-at-parallel-splits: that classifies damage three and shows larger damage is born only at parallel splits; this is the existence statement that would give tree domination a termination potential.
  edge-split-descendant-dissections-are-tree-dominated: that is tree domination (TD); this is a candidate local invariant for the termination of bh-free-54's least-damage recursion, not TD itself.
---

**REFUTED** (2026-09-19) by `no-median-need-have-damage-at-most-three`.
- **The counterexample.** A 17-piece descendant dissection of `Δ` in which every median
  has a straddler of least damage `4`. bh-free-54 found it (acb6bede1), and
  bh-major-mcg-2 re-checked it exactly.
- **Frequency.** SC₂ fails at 6 of 18018 rank-3 recursion nodes and 10 of 36670 rank-4
  nodes.
- **Tree domination is untouched.**

The original status follows.

Original status: **OPEN** (lane bh-major-mcg-2, 2026-09-19). Conjecture SC₂, with evidence from three
nodes. A full test is running (bh-free-54's damage logging over the rank-3 and rank-4
recursion nodes).

## Statement (SC₂)

Let `g` be a cell with `m = 2`, and `D` a descendant dissection of `g`. Some median `M`
of `g` has `δ_M(r) ≤ 3` for every piece `r ∈ D`, in the notation of
`median-cut-damage-is-born-at-parallel-splits`. Equivalently, every straddler of `M`
has values in one of the following classes, up to sign and permutation:
- `(1, −1, 0)`, single-cut;
- `(1, 1, −1)`, double midpoint;
- `(2, −1, 0)`, off by one.

In frame form: some row pair `(i, j)` has the property that, for every piece's frame
`X` in `g`'s coordinates, `row_i(X)` and `row_j(X)` are comparable or differ by a vector
in these classes.

## Evidence

- **The three logged nodes.** In the three `no_sc` nodes of
  `no-median-need-be-single-cut-for-a-descendant-dissection`, two medians have damage
  exactly `3`, and the only damage-3 pieces are double-midpoint pieces.
- **Split trees.** They satisfy SC₂ trivially: the root median has no straddlers.

## What is known about a proof

- **Parallel splits.** By `median-cut-damage-is-born-at-parallel-splits`, a median fails
  SC₂ only through a piece that descends heavily through a parallel split. That is a
  split of a double-midpoint or off-by-one ancestor along an edge the median does not
  cross.
- **Choosing the median locally fails.** The same node's five-piece example has a
  median that is clean at the centroid but has damage `4`. So a proof cannot pick the
  median at `c`, as `some-median-is-single-cut-at-the-centroid` does for SC at `c`.
- **The first test of a proof.** Show that parallel splits cannot occur heavily across
  all three medians at once. The obstruction would be a dissection whose pieces come
  from three far-edge splits, one across each median.

## Why it matters

- **Recursion cost.** If SC₂ holds, each round of the top-down TD recursion of
  `edge-split-descendant-dissections-have-single-cut-first-splits` costs at most two
  splits per straddler.
- **What else termination needs.** A measure bounding the rounds, plus inheritance.
  This is bh-free-54's line.

## Lesson for general BH

- **Bounded damage is the right shape.** When zero-damage cuts fail in a non-LCM
  operad, the next invariant to test is bounded damage, with a birth certificate for
  every violation.
- **What SC₂ reduces to.** Here that certificate is a parallel split. So SC₂ asks
  whether parallel splits can be spread across all three generator cuts in a single
  dissection.
