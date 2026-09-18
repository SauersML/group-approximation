import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindCell
import GroupApproximation.Meta.AxiomGuard

/-!
# The arc-keeping winding statement on pockets of relator cells: clause 5 discharged

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-82.

Target: `gfaceWindCell_NineStatement` (`GFaceWindCell.lean`), the arc-keeping winding statement
`gfaceWindNine_Statement` with the extra premise `gfaceWindCell_RCells K`.  **NOT CLOSED.**

## What the r-cell premise buys, exactly

In `gfaceWindNine_Arcs K` the relator cells of `X` occur in clause 4 only through `K.source`
(a relator cell by the structure `PocketFaceSet`) and in clause 5 (`gfaceWindNine_C5`).  So the
premise `gfaceWindCell_RCells K` can only act on clause 5, and it discharges it completely:

* every reached walk `c` is a sub-list of the pocket walk `∂K` (`gfaceWindCellNine_sub`, from
  the invariant `gfaceWind_reach_pair`);
* so a NONEMPTY reached walk has a dart `x ∈ c ∩ ∂K`, whose face `faceOf x ∈ K.faces` is a
  relator cell under `gfaceWindCell_RCells K`, and clause 5 holds with the empty adjacency path
  (`gfaceWindCell_c5`); see `gfaceWindCellNine_c5`;
* a walk containing a dart of either arc is nonempty (`gfaceWindCellNine_ne_nil`).

This is exactly how the r-cell premise rules out the Nine counterexample of lane gl-p10-73
(`sig = [6,14,0,19,9,4,18,1,5,7,12,2,13,11,16,15,3,17,10,8]`, outer face `3`, `K = {1,2,4}`):
there the faces `1, 2` of `K` are `0`-cells, which is what makes clause 5 fail on the arc-keeping
states (`gfaceWindCell_RCells K` is false there, so it is outside the target's domain).

## Route

* `gfaceWindCellNine_Arcs K` (definition): `gfaceWindNine_Arcs K` with clause 5 replaced by
  "an arc is nonempty, or `c ≠ []`".
* `gfaceWindCellNine_arcs_of` (proved): with `gfaceWindCell_RCells K` it gives
  `gfaceWindNine_Arcs K`.  `gfaceWindCellNine_of_arcs` (proved, no r-cell premise needed): the
  converse, since clause 5 forces `c ≠ []` (for `c = []` the face function is `0` by
  `gfaceWindSix_nil`, so no relator cell has value `1`, and no dart lies on `c`).
* `gfaceWindCellNine_Statement` (OPEN): under the premises of `gfaceWindCell_NineStatement`,
  `gfaceWindCellNine_Arcs K`.
* `gfaceWindCellNine_nine_of` (proved): `gfaceWindCellNine_Statement → gfaceWindCell_NineStatement`.
* `gfaceWindCellNine_of_nine` (proved): the converse.
* `gfaceWindCellNine_extremal_of` (proved): with `gfaceWindCell_CollapseStatement`, it gives
  `extremalGFaceProve_Statement`.

## Strength (LOUD)

**LOUD: `gfaceWindCellNine_Statement` is LOGICALLY EQUIVALENT to `gfaceWindCell_NineStatement`**
(both directions proved: `gfaceWindCellNine_nine_of`, `gfaceWindCellNine_of_nine`).  It is
**strictly smaller in proof content only**: clause 5, the only clause on which the r-cell
premise acts, is gone, and the nonemptiness of `c` is automatic when an arc is nonempty.  It is
NOT strictly weaker in logical strength; no residual with a proved `_of_` reduction to the
target can be.  The premise `gfaceWindCell_RCells K` is kept in the residual (unused by its
conclusion) so that its domain, and hence its truth, is exactly the target's.

## Remaining gap

The residual is the pure planar winding content of Nine: a NONEMPTY excision sequence from
`(∂K, 1_K)` that never excises a dart of the inverse source arc or of the target arc, ending at
a `0/1` (or vertex-simple, `g ≥ 0`) state, with clause 4 for an empty source arc and a nonempty
walk when both arcs are empty.  The only corpus route to the terminal state
(`gfaceWindSix_iter` from `gfaceWindSix_PosStep`, open through `gfaceWindSel_Statement`) does not
keep the arcs, and the one-step routes are exactly the loop choices, excluded by
`¬ gfaceChoose_Loop K`.

## Truth check

* The residual is equivalent to the target on the same domain (above), so the target checks
  carry over: scratchpad `gl-p10-78/cellcheck.py` (Lean-exact model, relator cells
  `K.faces ∪ {source}`, no-loop cases) finds an arc-keeping state in 47921, 53179, 28118 of
  47921, 53179, 28118 cases; rerun by this lane with random seed 11 (scratchpad
  `gl-p10-82/cell_rand11.txt`).
* Nine counterexample (gl-p10-73): outside the domain (`0`-cells `1, 2` in `K`), as above.
* The 18-dart counterexample of `GFaceWindSel.lean` (`sigma = [3,4,1,16,12,8,11,17,14,0,15,10,
  13,5,7,9,6,2]`) is a reached walk state with no CLEAN lobe; it refutes the lobe-selection
  statement `gfaceWindEight_Statement`, not the existence of an arc-keeping sequence, and the
  target and the residual do not use Eight, Chord, Ten, Eleven, Twelve or Thirteen.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section CellNine

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A reached walk is a sub-list of the pocket walk**, with the coboundary and base-face parts
of the invariant. -/
theorem gfaceWindCellNine_sub (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {c : List X.toCombMap.Dart} {g : X.toCombMap.Face → ℤ}
    (hr : Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g)) :
    (∀ x ∈ c, x ∈ K.boundary.cycle) ∧
      (∀ d, g (X.toCombMap.faceOf d) - g (X.toCombMap.faceOf (X.toCombMap.alpha d)) =
        gfaceWind_lind c d - gfaceWind_lind c (X.toCombMap.alpha d)) ∧
      g X.outerFace = 0 := by
  have hc := K.boundary.cycle_mem_iff
  have h0 : gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace K.boundary.cycle
      (gfaceWind_ind K.faces) :=
    gfaceWind_inv_start (fun d => (hc d).symm) hK.1 K.outerFace_not_mem
  obtain ⟨⟨hfil, -, hcob, ho⟩, -⟩ :=
    gfaceWind_reach_pair X.planar K.boundary.cycle_nodup hr h0
  refine ⟨fun x hx => ?_, hcob, ho⟩
  have hx' : x ∈ K.boundary.cycle.filter (gfaceWind_mem c) := by
    rw [hfil]
    exact hx
  exact (List.mem_filter.mp hx').1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCellNine_sub

/-- **A walk containing the arcs is nonempty when an arc is.** -/
theorem gfaceWindCellNine_ne_nil (K : PocketFaceSet D eps X lo hi) {c : List X.toCombMap.Dart}
    (hs : ∀ d ∈ invDarts X K.sourceArc.darts, d ∈ c) (ht : ∀ d ∈ K.targetArc.darts, d ∈ c)
    (h : K.sourceArc.darts ≠ [] ∨ K.targetArc.darts ≠ [] ∨ c ≠ []) : c ≠ [] := by
  rcases h with h | h | h
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ h
    exact List.ne_nil_of_mem (hs _ (gfaceWindNine_mem_src K hd))
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ h
    exact List.ne_nil_of_mem (ht d hd)
  · exact h
