---
rg: 2
id: edge-split-descendant-dissections-have-single-cut-first-splits
kind: claim
title: Every nontrivial descendant dissection of a unimodular cell has a first split of the cell whose plane cuts each straddling piece along one of that piece's own first splits
artifacts:
  - research/artifacts/gq-bh-major-mcg-2-single-cut-family.md
distinct_from:
  edge-split-descendant-dissections-are-tree-dominated: that is tree domination (TD), the statement to prove; this is a local invariant that, together with inheritance and finitely many cuts, gives TD by a top-down recursion in which every repair is a single edge split.
  edge-splits-cut-every-rational-hyperplane: that resolves an arbitrary rational plane inside a cell by a whole split tree; this asks that the planes of first splits of the ambient cell only ever meet a straddling piece along one of the piece's own first-split planes, so that one split resolves it.
  split-tree-restrictions-to-a-child-need-not-be-split-trees: that is one instance, repaired by two single cuts; this proposes that such one-cut repairs always exist.
---

**OPEN** (lane bh-major-mcg-2, 2026-09-18). A conjecture with evidence, proposed as the
target of the bottom-up approach to TD. The reduction part below is a lane proof; one referee PASS for the reduction (bh-ref-engines, 2026-09-18).

## Statement (SC)

Notation of `edge-split-ore-iff-synchronization-and-tree-domination`. Let `g` be a cell
and `D ≠ {g}` a descendant dissection of `g`.

**(SC)** Some first split `E` of `g`, with plane `Π`, has the following property. For
every piece `r ∈ D` whose interior meets `Π`, the intersection `Π ∩ r` is a first-split
plane of `r`: `Π` contains all rays of `r` but two, `a` and `b`, and contains `a + b`.
Call such an `E` a *single-cut split* for `D`.

**(I), inheritance.** After such a round, the pieces of `D` on each side, with the
straddlers split once at `a + b`, all lie in `Desc` of that half of `g`.

## Reduction: SC and I with finitely many cuts give TD

Run the recursion:
- at a cell `g` with current dissection `D_g ≠ {g}`, choose a single-cut split `E`;
- split each straddler once, at `a + b`;
- recurse into the two halves with the pieces on each side.

**Claim.** If (SC) and (I) hold at every stage and the recursion performs finitely many
cuts, then it yields `T ∈ Trees(C)` refining `D` with `T|r ∈ Trees(r)` for every
`r ∈ D`. That is TD for `D`.

**Proof.**
- **`T` is a split tree.** The recursion builds `T` from `C` by first splits, one
  child at a time. By (I), each half's pieces are descendants of the half, so the
  recursion applies again there. It stops at cells `g` with `D_g = {g}`.
- **Termination.** Fragments arise only from cuts, and there are finitely many. So the
  fragments form a finite set of cells. A branch of the recursion strictly shrinks the
  current cell, so it reaches a cell equal to a fragment, where `D_g = {g}`.
- **Restrictions.** Each fragment of `r` is obtained from `r` by a sequence of single
  cuts. Each cut is a first split of the current fragment of `r`, since `Π ∩ f` is a
  first-split plane of `f`. So the fragments of `r` form a split tree of `r`, which
  is `T|r`. ∎

## Evidence

1. **The far-edge family** (artifact; exact, one MSI process). This is every
   combination of minimal resolutions of the unit-corner lines `(1,−1,2)` in `K_a` and
   `(2,−1,1)` in `K_b`, in the far-edge sub-case of LD_atom.
   - 7 of the 9 combinations restrict to split trees on both halves of `E_{01}`.
   - The two that fail (`stt/tss`, and the example `tts/sst` of
     `split-tree-restrictions-to-a-child-need-not-be-split-trees`) each have two
     single-cut splits of `H_1`. One round of single cuts makes the restriction a split
     tree.
   - The third first split of `H_1` is not single-cut.
2. **The stellar split `Z`** (hand).
   - The median `x_0 = x_1` of `Δ` cuts only `cone(e_0, e_1, c)`, along its own first
     split at `v_{01}`.
   - Each half then has a two-piece dissection. It is the split at `c = v_{01} + e_2`.
   - So `Z` is dominated by 4 pieces.
3. **bh-free-54's least-damage runs** (`edge-split-descendant-dissections-are-tree-dominated`).
   - Named instances: `Z`, `M`, `M′`, the 9-piece prime, and the restriction in item 1.
     In each, leaves minus pieces equals the number of cuts (1, 2, 2, 4, 2), so every cut
     was a single edge split.
   - No synchronization step (a failure of (I)) occurred in any instance, named or
     random, in ranks 3 and 4. That count was reported to this lane by bh-free-54 and
     was not re-run here.

## What is missing

- A proof of (SC). It is false for an arbitrary rational plane, which can meet a piece
  anywhere. So a proof must use that `Π` is a median of `g` and that the pieces descend
  from `g`.
- A proof of (I).
- A bound on the number of cuts. A cut piece's two halves go to different sides, so the
  piece count per branch need not drop when every whole piece lies on one side.

## Lesson for general BH

- **Look for a least-damage cut.** For non-LCM dissection operads, tree domination may
  come from a "least-damage cut" invariant: the ambient cell always has a first split
  that meets every straddling piece only along one of that piece's own first splits.
- **What it buys.** Repairs are then single edge splits, and the tree is built top-down
  with no synchronization.
- **Evidence and gap.** It is the pattern in every computed case. It turns TD into one
  local geometric statement (SC), plus inheritance and a cut count.

## Referee (bh-ref-engines, 2026-09-18): the reduction PASSES; (SC), (I) and the cut bound remain open, as stated

- **The claim holds.** Assume (SC) and (I) at every stage and finitely many cuts. Then the recursion gives a
  split tree `T` of `C` refining `D`, with `T|r ∈ Trees(r)`.
  - Each round splits the current cell by one of its own first splits.
  - Each straddler is split along one of its own first-split planes. So the fragments of every `r` form a
    split tree of `r`.
- **The termination step should be phrased as follows.**
  - The set `P` of all pieces and fragments ever created is finite.
  - Each current cell is the union of its current pieces, which form a subset of `P`, and cells strictly
    decrease along a branch.
  - So a branch has at most `2^|P|` steps, and it stops exactly when `D_g = {g}`.
  - "Reaches a cell equal to a fragment" is true but needs this count.
- **Evidence.** Items 1–2 are consistent with the claim. Item 3 is reported from another lane and was not
  re-run here.
