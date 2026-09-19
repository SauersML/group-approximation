---
rg: 2
id: no-median-need-be-single-cut-for-a-descendant-dissection
kind: claim
title: A fourteen-piece descendant dissection of the triangle cone has no median that cuts every straddling piece along one of the piece's own first splits
artifacts:
  - research/artifacts/gq-bh-major-mcg-2-sc-counterexamples.md
distinct_from:
  edge-split-descendant-dissections-have-single-cut-first-splits: that conjectured (SC), that some median is always single-cut; this is an exact counterexample, one of 148 found by bh-free-54's logging run.
  some-median-is-single-cut-at-the-centroid: that proves some median is good at the centroid, and this example agrees with it; the failures here are away from the centroid, mostly at pieces the median crosses without meeting a vertex.
  edge-split-descendant-dissections-are-tree-dominated: that is tree domination (TD), which this does not touch; bh-free-54's least-damage recursion dominated every non-tree instance, including the nodes where SC fails.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-19). An explicit finite example, checked
by exact arithmetic (artifact; one MSI process, seconds). It was found by bh-free-54's
`sclog.py` run and re-checked here with independent code. No priority claimed.

## What `no_sc` measures

`sclog.py` (in `research/artifacts/gq-bh-free-54-spine-computation.md`) calls a node of
the least-damage recursion SC when some first split `(i, j)` of the node's cell `C` has
the following property: every fragment crossing the plane `y_i = y_j` is resolved by the
cut lemma into exactly two cells.

That is the same as (SC) of `edge-split-descendant-dissections-have-single-cut-first-splits`:
- The planes `y_i = y_j` are the three medians of `C`.
- A straddler resolves into two cells exactly when the plane is one of its first-split
  planes. Its values are then `(s, −s, 0)`, and the cut-lemma rule splits that edge
  first.
- The fragments at a node all descend from `C` (checked here for the logged nodes).

So each of the 148 rank-3 `no_sc` nodes (of 14086) is a counterexample to (SC), provided
its data are right. The three logged nodes were re-checked, and all three are.

## Statement

Take the following 14 cells, given by their rays. They form a descendant dissection `D`
of `Δ = cone(e_0, e_1, e_2)`: every piece is unimodular and lies in `Desc(Δ)`, the pieces
are pairwise interior-disjoint, and their weights sum to `1`.

```
(0,0,1) (0,1,0) (1,0,4)     (1,0,1) (1,1,0) (2,0,3)     (1,1,0) (2,2,1) (3,4,0)
(0,1,0) (1,0,2) (1,0,3)     (1,0,2) (1,1,0) (2,0,3)     (1,1,1) (1,2,0) (2,3,0)
(0,1,0) (1,0,2) (1,1,1)     (1,0,2) (1,1,0) (2,2,1)     (1,1,1) (2,2,1) (2,3,0)
(0,1,0) (1,0,3) (1,0,4)     (1,0,2) (1,1,1) (2,2,1)     (2,2,1) (2,3,0) (3,4,0)
(0,1,0) (1,1,1) (1,2,0)     (1,0,0) (1,0,1) (1,1,0)
```

**No median of `Δ` is single-cut for `D`.** Here is one bad straddler for each median,
with the values of the median's form on the piece's rays:

| median | form | straddler | values | how the median crosses it |
|---|---|---|---|---|
| `x_1 = x_2` | `x_2 − x_1` | `(0,1,0) (1,0,2) (1,1,1)` | `−1, 2, 0` | through the vertex `c`, with the wrong mediant |
| `x_0 = x_2` | `x_0 − x_2` | `(1,0,2) (1,1,0) (2,0,3)` | `−1, 1, −1` | through the midpoints of two edges, missing every vertex |
| `x_0 = x_1` | `x_1 − x_0` | `(0,1,0) (1,0,2) (1,0,3)` | `1, −1, −1` | through the midpoints of two edges, missing every vertex |

So (SC) is false. This is example 3 of the logged nodes, transported to `Δ` by its frame.
Examples 1 and 2 (15 and 18 pieces) behave the same way.

## Consistency with the landed lemmas

- **At the centroid.** `some-median-is-single-cut-at-the-centroid` predicts a median good
  at `c`. Here `x_1 = x_2` fails at `c`, and the other two medians are good there.
- **The criterion.** The two failures away from `c` are of the kind that
  `single-cut-is-a-mediant-condition-along-the-median` (part 1) calls never single-cut: a
  straddler with no ray on the median.
- **A gap in my mid-median node.** The consequence section of
  `mid-median-bad-cuts-need-a-badly-cut-creating-ancestor` ignored straddlers with no
  vertex on the median. Its lemma about bad cuts at vertices is unaffected, but its
  equivalence with (SC) is not.

## The damage is small (three nodes, exact)

Let the *damage* of a median be the largest number of pieces the cut lemma needs to
resolve one straddler. (SC) asks for damage `2`.

In all three logged nodes:
- one median has damage 8 to 10;
- the other two have damage exactly `3`. Every bad straddler of those two medians has
  values `±(1, −1, −1)`: a *double-midpoint piece*, crossed at the midpoints of two
  edges. Two edge splits resolve it: the first creates a vertex on the median, and the
  child containing it is single-cut there.

**Open question (SC₂).** Does every descendant dissection have a median of damage at most
`3`, with double-midpoint pieces as the only extra damage? This is evidence from three
nodes only. bh-free-54's `sclog.py` can log the minimum damage over medians at all 14086
nodes; that has been requested.

## What this does and does not affect

- **TD is untouched.** bh-free-54's least-damage recursion dominated all 262 rank-3
  non-tree instances in the same run, including the nodes where SC fails.
- **SC was never needed for the reduction.** In the reduction of
  `edge-split-descendant-dissections-have-single-cut-first-splits`, the restriction
  `T|r ∈ Trees(r)` holds for any cut-lemma resolution of the straddlers, since each is a
  split tree of its piece. (SC) was meant only as a termination measure: one split per
  straddler. With it gone, TD needs the inheritance step and termination by another
  measure, which is bh-free-54's line.

## Lesson for general BH

- **The least-damage cut is not damage-free.** Even with all pieces descending from the
  cell, all three first cuts can hit pieces badly.
- **The typical bad piece meets the cut at no vertex.** In the three logged nodes, the
  two medians that are clean at the centroid fail only at double-midpoint pieces, and
  two splits resolve each of them.
- **A bounded-damage invariant, not zero damage.** For non-LCM dissection operads, the
  right target is "some generator cut needs at most two splits per piece". It is a
  potential for termination, not a rearrangement.
- **Name what a logged counter measures.** Read the logging code before interpreting a
  counter, and pin its definition to the statement it tests. Here `no_sc` turned out to
  be exactly the conjecture, so its 148 hits were refutations, not noise.
