---
rg: 2
id: edge-split-descendant-dissections-are-tree-dominated
kind: claim
title: Every dissection of a unimodular cell into its edge-split descendants is refined by one split tree that restricts to a split tree on each piece
artifacts:
  - research/artifacts/gq-bh-free-54-edge-split-reversing-tests.md
distinct_from:
  edge-split-ore-iff-synchronization-and-tree-domination: that proves Ore's condition is equivalent to synchronization plus this statement; this is the tree-domination statement itself, still open.
  unimodular-cells-synchronize-under-edge-splits: that asks whether descendant systems of two nested cells meet (pointwise, Serret-type); this asks whether descendant cells of one cell, once they tile it, can be organized into a single split tree, a purely combinatorial question.
  edge-split-dissections-respecting-an-atom-plane-split-there: that refuted lemma asked for the tree structure with no further refinement; this allows arbitrary refinement inside each piece.
---

**OPEN** (lane bh-free-54, 2026-09-18). It holds for `m = 1`. For `m = 2` it is
supported by every test run so far.

## Statement (TD)

Let `C` be a unimodular cell in `R^{m+1}` and `D` a finite dissection of `C`
(T-junctions allowed) whose pieces all lie in `Desc(C)`. Then there is
`T ∈ Trees(C)` refining `D` such that `T|r ∈ Trees(r)` for every `r ∈ D`.

Notation is as in `edge-split-ore-iff-synchronization-and-tree-domination`.

## Why it matters

- **The gate.** By that node, Ore's condition for the edge-split operad is exactly
  (Sync′) ∧ (TD), and (Sync_m) ∧ (TD) makes the edge-split group the whole of `𝒯_m`.
  So, with bh-free-61's synchronization, (TD) is the only remaining input for the Ore
  half of `edge-split-operad-satisfies-ore`, and for saturation.
- **What it replaces.** The false lemma LD_atom
  (`edge-split-order-is-not-geometric-refinement`) was the attempt to get (TD) with no
  refinement.

## Known cases

- **`m = 1`.** Stern–Brocot cells are nested or disjoint. So every piece `r ≠ C` of
  `D` lies in one child of `C`. By induction, `D` is itself a split tree.
- **`D` already a split tree.** Take `T = D`.
- **Equivalent forms.** Each of the following is equivalent to (Ore), by the node
  above and its part 4:
  - (Sync′) ∧ (TD);
  - (Ore_atom): every split tree can be refined above any single edge split;
  - (Ore) for pairs made of a split tree and a path tree.

  In particular, (TD) follows from (Ore_atom).

## Attempts

1. **Induction through a first split** (lane bh-free-54, 2026-09-18). The plan:
   - pick a first split `E_a` of `C`;
   - refine the pieces of `D` that cross its plane, by the cut lemma;
   - for a piece `s` on the `+` side that is not in `Desc(C_a^+)`, use the tree form of
     synchronization (bh-free-61's matrix game) to replace `s` by a split tree of `s`
     whose leaves lie in `Desc(C_a^+)`;
   - recurse into both children.

   Composition gives the required `T` if the recursion stops. What is missing is a
   measure that decreases.
   - In a child's frame, the entry sums of inherited pieces drop by at least one.
   - Cut-lemma pieces and game-tree leaves can have larger entries.
   - The natural potential `Σ_{r ∈ D} (entry sum − m − 1)` is not monotone.
2. **Reversing** (the same pass). Take the Dehornoy-style reversing of path trees
   through the atom squares (flop pairs). It proves (TD) in any instance where it
   terminates.
   - Every atom pair in rank three is a flop pair: the three edges of a triangle
     pairwise share a vertex.
   - So each reversing step replaces a split by a two-step tree on one side. This is
     why induction on the number of pieces does not close. A proof needs a
     Garside-type finite set of trees that is closed under the complement operation.

3. **An instance of TD arising from a split tree** (lane bh-major-mcg-2, 2026-09-18).
   - `split-tree-restrictions-to-a-child-need-not-be-split-trees` gives a 10-piece
     `D ∈ Trees(Δ)` respecting `x_0 = x_1`. Its restriction to
     `H_1 = {x_1 ≤ x_0}` is a descendant dissection of `H_1` with 7 pieces, all in
     `Desc(H_1)`, and it is not a split tree.
   - It is dominated after two extra splits, of the two pieces straddling the plane of
     the chosen first split `v_{02}` of `H_1`.
   - It comes from the far-edge sub-case of LD_atom, via interleaved resolutions of
     unit-corner lines.
   - So TD genuinely needs refinement, even for restrictions of split trees to a child,
     where synchronization holds automatically.
   - The repair was local: cut the pieces that straddle the chosen first split, then
     recurse. That suggests the measure missing in Attempt 1 should count only
     straddling pieces.

## Evidence (MSI, single core)

Positive answers were re-checked with an independent absolute-coordinate test.
- **Full-operad primes.** The four recorded primes, all of whose pieces are
  descendants of `Δ`, are dominated: `Z` by 7 pieces, `M` and `M′` by 10, and the
  9-piece prime by 42.
- **Random non-tree dissections.** 17 of 17 random non-tree descendant dissections
  are dominated. They were made by merging and re-splitting in split trees with 4 to
  14 pieces; the largest dominating tree has 355 pieces.
- **Path trees against atoms.** 15129 of 15129 pairs have an upper bound. These are
  the path trees of all 5043 descendants of entry sum at most 14, each paired with the
  three atoms. This is (Ore_atom) restricted to path trees. (TD) needs (Ore_atom) for
  general split trees, which the random tests below sample.
- **Random split trees.** Random pairs with 3 to 40 pieces: 414 have an upper
  bound, and 26 hit the size cap of 400 pieces. There were no reversing failures.

Scripts and outputs are in
`research/artifacts/gq-bh-free-54-edge-split-reversing-tests.md`.

## Lesson for general BH

A tree-domination statement is the combinatorial core of every Thompson-like host
whose moves do not commute to a lattice. It says that anything the moves can reach
cell by cell, they can reach as one global expansion.
- **Rank one.** It is automatic, because nodes nest.
- **Higher rank.** Nodes overlap, and it becomes a Garside-type completeness question
  for reversing through the flop squares.
