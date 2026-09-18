import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.BlkBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.PlaceLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Placement of the removed block of a lobe move: the automatic cases

Lane gl-p10-56.  The clauses of `roseLobeBlk_BlockStatement` that need no planarity, for a lobe
colouring `z = roseJunctionCore_lobeColour M (walkKeep M c) rs`:

* *inner lobe* (all roots have faces in the face set): the source cell is never flipped in, since
  a face class never changes membership in the face set (`roseLobePlace_src_of`);
* *lake* (a single root `r` with face outside the face set): the kept cell is never flipped out
  (`roseLobePlace_kept_of`), and no dart of the source arc or of the target arc is removed, so both
  placement clauses hold (`roseLobePlace_place1_of_side`, `roseLobePlace_place2_of_side`);
* *non-bubble removed block*: if the cycle is `A ++ B ++ C` with a contiguous removed block and
  some dart of `B` lies outside the arc, the filtered arc is an infix of the arc
  (`roseLobePlace_place1_of_esc`, `roseLobePlace_place2_of_esc`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

section Colour

variable {M : CombMap.{v}}

/-- **An inner lobe colours nothing outside the face set.** -/
theorem roseLobePlace_inner_eq_false {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {rs : List M.Dart}
    (hin : ∀ r ∈ rs, M.faceOf r ∈ faces) {x : M.Dart} (hx : M.faceOf x ∉ faces) :
    roseJunctionCore_lobeColour M (walkKeep M c) rs x = false := by
  refine roseJunctionCore_lobeColour_eq_false M _ fun r hr h => hx ?_
  exact (P10Rose.faceOf_mem_iff_of_walkEqvGen hc h).mp (hin r hr)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_inner_eq_false

/-- **A lake colours nothing inside the face set.** -/
theorem roseLobePlace_lake_eq_false {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {rs : List M.Dart}
    {r : M.Dart} (hrs : rs = [r]) (hr : M.faceOf r ∉ faces) {x : M.Dart}
    (hx : M.faceOf x ∈ faces) :
    roseJunctionCore_lobeColour M (walkKeep M c) rs x = false := by
  subst hrs
  refine roseJunctionCore_lobeColour_eq_false M _ fun r' hr' h => ?_
  rw [List.mem_singleton] at hr'
  subst hr'
  exact hr ((P10Rose.faceOf_mem_iff_of_walkEqvGen hc h).mpr hx)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_lake_eq_false

end Colour

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The source clause, automatic for an inner lobe.** -/
theorem roseLobePlace_src_of (K : PocketFaceSet D eps X lo hi) {rs : List X.toCombMap.Dart}
    (h : (∀ r ∈ rs, X.toCombMap.faceOf r ∈ K.faces) ∨
      (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) :
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) := by
  rcases h with hin | h
  · exact P10Rose.FilterMove.not_mem_flipFaces
      (roseJunctionCore_lobeColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)
      K.source_not_mem fun x hx => roseLobePlace_inner_eq_false K.boundary.cycle_mem_iff hin
        (by rw [hx]; exact K.source_not_mem)
  · exact h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_src_of

/-- **The kept clause, automatic for a lake.** -/
theorem roseLobePlace_kept_of (K : PocketFaceSet D eps X lo hi) {rs : List X.toCombMap.Dart}
    (h : (∃ r, rs = [r] ∧ X.toCombMap.faceOf r ∉ K.faces) ∨
      (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) :
    (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) := by
  rcases h with ⟨r, hrs, hr⟩ | h
  · exact P10Rose.FilterMove.mem_flipFaces
      (roseJunctionCore_lobeColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)
      K.kept_mem fun x hx => roseLobePlace_lake_eq_false K.boundary.cycle_mem_iff hrs hr
        (by rw [hx]; exact K.kept_mem)
  · exact h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_kept_of

/-- **A lake colours no dart of the exterior face**: by the root clause, a single root off the
walk has no face-class chain to the exterior face, and a root on the walk has its face in the face
set. -/
theorem roseLobePlace_lake_outer (K : PocketFaceSet D eps X lo hi)
    {rs : List X.toCombMap.Dart} {r : X.toCombMap.Dart} (hrs : rs = [r])
    (hr : X.toCombMap.faceOf r ∉ K.faces)
    (hroot : (rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
      ∃ r, rs = [r] ∧
        (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
        ∃ y ∈ K.boundary.cycle, Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
          Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y))
    {d : X.toCombMap.Dart} (hd : X.toCombMap.faceOf d = X.outerFace) :
    roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs d =
      false := by
  rcases hroot with ⟨-, hall⟩ | ⟨r', hr', hno, -⟩
  · subst hrs
    exact absurd ((K.boundary.cycle_mem_iff r).mp (hall r (List.mem_singleton_self r))).1 hr
  · subst hr'
    refine roseJunctionCore_lobeColour_eq_false _ _ fun r'' hr'' h => ?_
    rw [List.mem_singleton] at hr''
    subst hr''
    exact hno d hd h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_lake_outer

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
