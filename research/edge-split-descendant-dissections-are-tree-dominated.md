---
rg: 2
id: edge-split-descendant-dissections-are-tree-dominated
kind: claim
title: Every dissection of a unimodular cell into its edge-split descendants is refined by one split tree that restricts to a split tree on each piece
artifacts:
  - research/artifacts/gq-bh-free-54-edge-split-reversing-tests.md
  - research/artifacts/gq-bh-free-54-tree-domination-tests.md
  - research/artifacts/gq-bh-free-54-sc2-damage-tests.md
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
4. **The cut-and-synchronize recursion: the split rule decides everything** (lane
   bh-free-54, 2026-09-18). The recursion `td(C, F)` runs on fragments `F` tiling `C`,
   all in `Desc(C)`:
   - stop if `F = {C}`;
   - otherwise choose a first split `s` of `C`;
   - cut every fragment straddling its plane, using the cut lemma;
   - replace every fragment that lies in a child without descending from it by a
     synchronization tree (bh-free-61's braid-cut game);
   - recurse into both children.

   **Correctness.** Each piece `r` of `D` is only ever refined by split trees of its
   own fragments. So on termination the leaves `T` satisfy `T ∈ Trees(C)` and
   `T|r ∈ Trees(r)` for every `r`. So TD follows from termination of `td` for some
   rule choosing `s`. Two rules were tested:
   - **R1, follow the deepest.** Take `s` to be one descent step of the fragment with
     the largest entry sum. **It runs away.** In rank 3, 19 of 23 random non-tree
     instances hit the caps (up to 179549 cuts and 23859 synchronizations). In rank 4,
     18 of 70 did.
   - **R2, least damage.** Minimise twice the number of straddling fragments plus the
     number of non-inherited ones. **In this run it always terminated, with a small
     repair.**
     - Rank 3: 23 of 23 random instances, at most 5 cuts, depth at most 13, and at
       most 1.27 times as many leaves as pieces.
     - Rank 4: 70 of 70 random instances, at most 7 cuts, and at most 1.83 times as
       many leaves as pieces.
     - All named instances. `Z` gives 4 leaves (1 cut), `M` and `M′` give 8 each
       (2 cuts), the 9-piece prime gives 13 (4 cuts), and bh-major-mcg-2's 7-piece
       restriction gives 9 (2 cuts, matching its hand repair).
     - **No synchronization was needed under R2 in this run.** Every cut fragment
       landed in the descendant set of its child. (Later rank-4 runs did need it; see
       Attempt 5.)

   **Conjecture (TD-LD).** The least-damage recursion terminates on every
   descendant dissection. It would imply (TD), and then Ore's condition given (Sync_m).

   **What a proof needs.** A potential that R2 decreases. It cannot be the entry sums
   of fragments, since R1 decreases the deepest one and diverges. It should count
   straddling pairs, as Attempt 3 suggested.

   **Why no synchronization in rank 3.** By the vertex and facet lemmas of
   `rank-two-synchronization-off-totally-irrational-rays`, a fragment of a child that
   shares a ray with it descends from it. So synchronization can only be forced by
   fragments that meet no ray of the child. Least damage counts such fragments, and
   in every test it found splits that create none.
5. **Local damage bounds fail; R2 still terminates** (lanes bh-free-54 and
   bh-major-mcg-2, 2026-09-18/19).
   - **Larger runs of R2.**
     - SLURM job 1329260 (`sclog.py`): rank 3, 262 of 262; rank 4, 668 of 671.
     - Direct pinned run (`sc2.py`): rank 3, 336 of 336; rank 4, 1412 of 1416.
     - The rank-4 caps were hit inside a synchronization or cut subroutine, at
       recursion depth at most 10. So they are not runaways of R2. But rank 4 does
       need synchronization, which rank 3 never did.
   - **SC (some first split cuts every straddler once) is false.**
     `no-median-need-be-single-cut-for-a-descendant-dissection` (bh-major-mcg-2,
     `5a5a8bd32`) gives it at 148 of 14086 rank-3 nodes, re-checked independently.
   - **SC₂ (some first split has damage at most 3) is false too.**
     `research/artifacts/gq-bh-free-54-sc2-damage-tests.md`:
     - rank 3, 6 of 18018 nodes; rank 4, 10 of 36670;
     - calibrated on rank 2 and on the three SC nodes, which have damage 3.
   - **Lemma A (Attempt 4 plan) fails at a few nodes.** Its requirement is a split with
     no non-inherited fragment and fewer fragments in each child. It failed at 2 of
     14086 rank-3 nodes and 4 of 29053 rank-4 nodes (job 1329260).
   - **Reading.** Every local invariant tried so far fails at a small fraction of
     nodes: bounded damage per split, and a strict drop in fragment count. R2
     terminates anyway, so its potential must be global, for example total damage
     summed over a whole subtree. The saved all-splits-bad nodes are the test bed
     (bh-major-mcg-2's parallel-split families).

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

- **Cut-and-synchronize recursion (Attempt 4)** (one msismall core, 495 s).
  - **Calibration.** In rank 2 (`m = 1`) it returns `T = D` exactly on 140 of 140
    split trees, with no cuts or synchronizations.
  - **Rank 3 random instances.** These are restrictions to a child of cut and
    synchronized random split trees: 1738 in all, of which 1715 are already trees.
  - **Rank 4 random instances.** Of 1024, 954 are already trees.
  - Scripts and outputs are in
    `research/artifacts/gq-bh-free-54-tree-domination-tests.md`.

## Lesson for general BH

A tree-domination statement is the combinatorial core of every Thompson-like host
whose moves do not commute to a lattice. It says that anything the moves can reach
cell by cell, they can reach as one global expansion.
- **Rank one.** It is automatic, because nodes nest.
- **Higher rank.** Nodes overlap, and it becomes a Garside-type completeness question
  for reversing through the flop squares.
- **Choose splits by damage, not by descent.** In the tests, the repair that
  tree domination needs is small and local exactly when each split is chosen to
  minimise the fragments it disturbs. Following one piece's descent path, which is
  the Garside-style normal-form instinct, diverges.
- **Bounded local repair is the wrong target.** SC and SC₂ fail at a fraction of a
  percent of nodes, yet the recursion finishes. So the termination proof for tree
  domination must use a global potential, not a per-node damage bound.
