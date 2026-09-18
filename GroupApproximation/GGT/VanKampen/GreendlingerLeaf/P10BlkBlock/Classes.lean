import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock.Premises
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.JunctionCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Move
import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The walk classes of the counterexample pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-88.

The walk `[0,15,2,8,6,4,13]` of `P10BlkBlockModel.pK` keeps every edge but `{10,11}`, and both
darts `10` and `11` lie on the face `[2,6,10,11]`.  So the classes of
`FaceClassStep (walkKeep …)` are exactly the seven faces, numbered by `faceClass`
(`eqvGen_iff`).

Proof route: `faceClass` is constant along a step (`decide`), and every dart is joined to the
representative `faceRep` of its face by face steps.  The lobe colouring of a list of roots `rs` is
then `decide (∃ r ∈ rs, faceClass r = faceClass x)` (`colour_eq`).  The flip of the source cell
`S = [3]` and of the kept cell `K₀ = [0,15,4]` is read off by
`P10Rose.FilterMove.mem_flipFaces_iff` (`srcFlip`, `keptFlip`).

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.P10BlkBlockModel

open SimpleClosedWalkSides (walkKeep)
open GreendlingerLeaf.P10RoseExtremalTrim (roseJunctionCore_lobeColour
  roseJunctionCore_lobeColour_eq_true_iff roseJunctionCore_lobeColour_step)
open GreendlingerLeaf.P10Rose.FilterMove (flipFaces mem_flipFaces_iff)
open GreendlingerLeaf.P10Rose.SubArcMove (bool_eq_of_iff)

/-- The darts on the edges of the walk: all but `10` and `11`. -/
def keepB : Fin 16 → Bool :=
  ![true, true, true, true, true, true, true, true, true, true, false, false, true, true, true,
    true]

/-- One step inside a walk class. -/
abbrev stepRel : diagram.toCombMap.Dart → diagram.toCombMap.Dart → Prop :=
  CombMap.FaceClassStep diagram.toCombMap (walkKeep diagram.toCombMap pK.boundary.cycle)

theorem keep_iff (x : diagram.toCombMap.Dart) :
    walkKeep diagram.toCombMap pK.boundary.cycle x ↔ keepB x = true := by
  unfold walkKeep
  revert x
  decide

theorem faceClass_facePerm : ∀ x : diagram.toCombMap.Dart,
    faceClass (diagram.toCombMap.facePerm x) = faceClass x := by
  decide

theorem faceClass_alpha_aux : ∀ x : diagram.toCombMap.Dart,
    keepB x = false → faceClass (diagram.toCombMap.alpha x) = faceClass x := by
  decide

theorem faceClass_alpha_of_not_keep (x : diagram.toCombMap.Dart)
    (hk : ¬walkKeep diagram.toCombMap pK.boundary.cycle x) :
    faceClass (diagram.toCombMap.alpha x) = faceClass x :=
  faceClass_alpha_aux x (Bool.eq_false_iff.mpr fun h => hk ((keep_iff x).mpr h))

theorem step_faceClass (x y : diagram.toCombMap.Dart) (h : stepRel x y) :
    faceClass x = faceClass y := by
  rcases h with h | ⟨hk, h⟩
  · rw [h, faceClass_facePerm]
  · rw [h, faceClass_alpha_of_not_keep x hk]

/-- Every dart is joined to the representative of its face by face steps. -/
theorem from_rep (x : Fin 16) : Relation.EqvGen stepRel (faceRep (faceClass x)) x := by
  have f {a b : diagram.toCombMap.Dart} (h : diagram.toCombMap.facePerm a = b) :
      Relation.EqvGen stepRel a b :=
    .rel _ _ (Or.inl h.symm)
  have t {a b c : diagram.toCombMap.Dart} (h1 : Relation.EqvGen stepRel a b)
      (h2 : Relation.EqvGen stepRel b c) : Relation.EqvGen stepRel a c :=
    .trans _ _ _ h1 h2
  have h15 : Relation.EqvGen stepRel 0 15 := f (by decide)
  have h4 : Relation.EqvGen stepRel 0 4 := t h15 (f (by decide))
  have h14 : Relation.EqvGen stepRel 1 14 := f (by decide)
  have h6 : Relation.EqvGen stepRel 2 6 := f (by decide)
  have h10 : Relation.EqvGen stepRel 2 10 := t h6 (f (by decide))
  have h11 : Relation.EqvGen stepRel 2 11 := t h10 (f (by decide))
  have h9 : Relation.EqvGen stepRel 5 9 := f (by decide)
  have h12 : Relation.EqvGen stepRel 7 12 := f (by decide)
  have h13 : Relation.EqvGen stepRel 8 13 := f (by decide)
  fin_cases x
  · exact .refl _
  · exact .refl _
  · exact .refl _
  · exact .refl _
  · exact h4
  · exact .refl _
  · exact h6
  · exact .refl _
  · exact .refl _
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- **The walk classes are the faces.** -/
theorem eqvGen_iff (r x : diagram.toCombMap.Dart) :
    Relation.EqvGen stepRel r x ↔ faceClass r = faceClass x := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact step_faceClass a b hab
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    have h1 := from_rep r
    have h2 := from_rep x
    rw [h] at h1
    exact .trans _ _ _ (.symm _ _ h1) h2

/-- **The lobe colouring** of the roots `rs` marks the faces of the roots. -/
theorem colour_eq (rs : List diagram.toCombMap.Dart) (x : diagram.toCombMap.Dart) :
    roseJunctionCore_lobeColour diagram.toCombMap (walkKeep diagram.toCombMap pK.boundary.cycle)
      rs x = decide (∃ r ∈ rs, faceClass r = faceClass x) :=
  bool_eq_of_iff ((roseJunctionCore_lobeColour_eq_true_iff _ _ rs x).trans
    ((exists_congr fun r => and_congr_right fun _ => eqvGen_iff r x).trans
      decide_eq_true_iff.symm))

/-- The flip of the face of a dart `x` under the lobe move of the roots `rs`. -/
theorem flipIff (rs : List diagram.toCombMap.Dart) (x : diagram.toCombMap.Dart) :
    diagram.toCombMap.faceOf x ∈ flipFaces diagram.toCombMap pK.faces
      (roseJunctionCore_lobeColour diagram.toCombMap
        (walkKeep diagram.toCombMap pK.boundary.cycle) rs) ↔
      (faceIn (faceClass x) = true ↔
        decide (∃ r ∈ rs, faceClass r = faceClass x) = false) := by
  rw [mem_flipFaces_iff (roseJunctionCore_lobeColour_step _
    (walkKeep diagram.toCombMap pK.boundary.cycle) rs) x, colour_eq]
  change (M.faceOf x ∈ pFaces ↔ _) ↔ _
  rw [faceOf_eq_face', face_mem_iff]

/-- **The source cell `S = [3]` flips exactly when a root lies on it.** -/
theorem srcFlip (rs : List diagram.toCombMap.Dart) :
    (Embedded.cell diagram pK.source).face ∈ flipFaces diagram.toCombMap pK.faces
      (roseJunctionCore_lobeColour diagram.toCombMap
        (walkKeep diagram.toCombMap pK.boundary.cycle) rs) ↔
      decide (∃ r ∈ rs, faceClass r = 3) = true := by
  have h := flipIff rs (faceRep 3)
  have h3 : faceIn (faceClass (faceRep 3)) = false ∧ faceClass (faceRep 3) = 3 := by decide
  rw [h3.1, h3.2] at h
  refine h.trans ?_
  generalize decide (∃ r ∈ rs, faceClass r = 3) = b
  cases b <;> decide

/-- **The kept cell `K₀ = [0,15,4]` flips exactly when no root lies on it.** -/
theorem keptFlip (rs : List diagram.toCombMap.Dart) :
    (Embedded.cell diagram pK.kept).face ∈ flipFaces diagram.toCombMap pK.faces
      (roseJunctionCore_lobeColour diagram.toCombMap
        (walkKeep diagram.toCombMap pK.boundary.cycle) rs) ↔
      decide (∃ r ∈ rs, faceClass r = 0) = false := by
  have h := flipIff rs (faceRep 0)
  have h0 : faceIn (faceClass (faceRep 0)) = true ∧ faceClass (faceRep 0) = 0 := by decide
  rw [h0.1, h0.2] at h
  refine h.trans ?_
  generalize decide (∃ r ∈ rs, faceClass r = 0) = b
  cases b <;> decide

/-- The darts of the walk lie on the faces `0`, `2` and `6`. -/
theorem cyc_class : ∀ r ∈ cyc, faceClass r = 0 ∨ faceClass r = 2 ∨ faceClass r = 6 := by
  decide

end GroupApproximation.GGT.VanKampen.P10BlkBlockModel

#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.keepB
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.stepRel
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.keep_iff
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceClass_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceClass_alpha_aux
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceClass_alpha_of_not_keep
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.step_faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.from_rep
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.eqvGen_iff
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.colour_eq
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.flipIff
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.srcFlip
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.keptFlip
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.cyc_class
