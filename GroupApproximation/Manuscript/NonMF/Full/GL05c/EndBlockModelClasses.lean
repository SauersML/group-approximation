import GroupApproximation.Manuscript.NonMF.Full.GL05c.Pocket
import GroupApproximation.Meta.AxiomGuard

/-!
# The face classes of the 16-dart counterexample to WO-GL05-2'

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane nm-gl05c-02.

The diagram `Model.diagram` (`GL05c/Diagram`) with the pocket `Model.pocketK` (`GL05c/Pocket`)
has boundary cycle `c = [8,12,10,0,2,6,4]`.  Its edges are all kept by `walkKeep c` except the loop
`e = {14,15}`.  So the classes of `FaceClassStep (walkKeep c)` are the faces, except that the source
cell `S` (face `5`, containing `14`) and the exterior `O` (face `6`, containing `15`) merge.

* `endBlockModel_cls`: the class index, `O ∪ S ↦ 5`, `P ↦ 0`, `R1 ↦ 1`, `Q1 ↦ 2`, `R2 ↦ 3`,
  `Q2 ↦ 4`.
* `endBlockModel_cls_of_eqvGen`: a face-class chain keeps `endBlockModel_cls` (both elementary
  steps do, checked by `decide` on `Fin 16`).
* `endBlockModel_eqvGen_of_cls`: darts with the same index are joined by a chain (same face, or
  through the step `14 → 15` across the unkept loop).
* `endBlockModel_colour`, `endBlockModel_movePred`: the colouring `regionColour` of every dart,
  and the move predicate, in closed form.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- The face class of each dart for the boundary cycle of `Model.pocketK`:
`P, R1, Q1, R2, Q2` are `0, ..., 4` and `O ∪ S` is `5`. -/
def endBlockModel_cls : Fin 16 → Fin 6 := ![0, 5, 1, 5, 1, 5, 2, 5, 3, 5, 3, 5, 4, 5, 5, 5]

/-- A face step keeps the class index. -/
theorem endBlockModel_cls_facePerm : ∀ x : Fin 16,
    endBlockModel_cls (Model.M.facePerm x) = endBlockModel_cls x := by
  decide

/-- An edge step across an edge off the cycle keeps the class index. -/
theorem endBlockModel_cls_alpha : ∀ x : Fin 16,
    ¬(x ∈ ([8, 12, 10, 0, 2, 6, 4] : List (Fin 16)) ∨
      Model.mapAlpha x ∈ ([8, 12, 10, 0, 2, 6, 4] : List (Fin 16))) →
    endBlockModel_cls (Model.mapAlpha x) = endBlockModel_cls x := by
  decide

/-- Equal class indices come from the same face, or from the faces `S` and `O`. -/
theorem endBlockModel_cls_cases : ∀ x y : Fin 16, endBlockModel_cls x = endBlockModel_cls y →
    Model.faceClass x = Model.faceClass y ∨
      (Model.faceClass x = 5 ∧ Model.faceClass y = 6) ∨
      (Model.faceClass x = 6 ∧ Model.faceClass y = 5) := by
  decide

/-- **One step of a face-class chain keeps the class index.** -/
theorem endBlockModel_cls_step {x y : Model.diagram.toCombMap.Dart}
    (h : CombMap.FaceClassStep Model.diagram.toCombMap
      (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) x y) :
    endBlockModel_cls x = endBlockModel_cls y := by
  rcases h with rfl | ⟨hk, rfl⟩
  · exact (endBlockModel_cls_facePerm x).symm
  · have hk' : ¬(x ∈ ([8, 12, 10, 0, 2, 6, 4] : List (Fin 16)) ∨
        Model.mapAlpha x ∈ ([8, 12, 10, 0, 2, 6, 4] : List (Fin 16))) := hk
    exact (endBlockModel_cls_alpha x hk').symm

/-- **A face-class chain keeps the class index.** -/
theorem endBlockModel_cls_of_eqvGen {x y : Model.diagram.toCombMap.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep Model.diagram.toCombMap
      (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle)) x y) :
    endBlockModel_cls x = endBlockModel_cls y := by
  induction h with
  | rel _ _ hs => exact endBlockModel_cls_step hs
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Two darts of the same face are joined by a face-class chain. -/
theorem endBlockModel_eqvGen_of_faceClass {x y : Model.diagram.toCombMap.Dart}
    (h : Model.faceClass x = Model.faceClass y) :
    Relation.EqvGen (CombMap.FaceClassStep Model.diagram.toCombMap
      (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle)) x y := by
  have hx := (Model.faceOf_eq_face x (Model.faceClass x)).mpr rfl
  have hy := (Model.faceOf_eq_face y (Model.faceClass x)).mpr h.symm
  exact eqvGen_faceClass_of_sameCycle Model.diagram.toCombMap _
    ((CombMap.faceOf_eq_iff Model.M x y).mp (hx.trans hy.symm))

/-- The loop `e = {14,15}` is not an edge of the boundary cycle. -/
theorem endBlockModel_not_walkKeep_14 :
    ¬walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle 14 := by
  have h : ¬((14 : Fin 16) ∈ ([8, 12, 10, 0, 2, 6, 4] : List (Fin 16)) ∨
      Model.mapAlpha 14 ∈ ([8, 12, 10, 0, 2, 6, 4] : List (Fin 16))) := by
    decide
  exact h

/-- The step `14 → 15` across the loop `e` joins `S` to `O`. -/
theorem endBlockModel_eqvGen_14_15 :
    Relation.EqvGen (CombMap.FaceClassStep Model.diagram.toCombMap
      (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle)) 14 15 :=
  Relation.EqvGen.rel _ _ (Or.inr ⟨endBlockModel_not_walkKeep_14, by decide⟩)

/-- **Darts with the same class index are joined by a face-class chain.** -/
theorem endBlockModel_eqvGen_of_cls {x y : Model.diagram.toCombMap.Dart}
    (h : endBlockModel_cls x = endBlockModel_cls y) :
    Relation.EqvGen (CombMap.FaceClassStep Model.diagram.toCombMap
      (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle)) x y := by
  rcases endBlockModel_cls_cases x y h with hf | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact endBlockModel_eqvGen_of_faceClass hf
  · exact Relation.EqvGen.trans _ _ _
      (endBlockModel_eqvGen_of_faceClass (y := 14) (hx.trans (by decide)))
      (Relation.EqvGen.trans _ _ _ endBlockModel_eqvGen_14_15
        (endBlockModel_eqvGen_of_faceClass (x := 15) (Eq.trans (by decide) hy.symm)))
  · exact Relation.EqvGen.trans _ _ _
      (endBlockModel_eqvGen_of_faceClass (y := 15) (hx.trans (by decide)))
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ endBlockModel_eqvGen_14_15)
        (endBlockModel_eqvGen_of_faceClass (x := 14) (Eq.trans (by decide) hy.symm)))

/-- **The colouring of the class of `r`**, in closed form: `true` exactly on the darts with the
class index of `r`. -/
theorem endBlockModel_colour (r d : Model.diagram.toCombMap.Dart) :
    GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r d =
      decide (endBlockModel_cls d = endBlockModel_cls r) := by
  by_cases h : endBlockModel_cls d = endBlockModel_cls r
  · rw [decide_eq_true h]
    exact (GL05b.regionColour_eq_true_iff _ _ _ _).mpr (endBlockModel_eqvGen_of_cls h.symm)
  · rw [decide_eq_false h]
    exact GL05b.regionColour_eq_false _ _ fun he => h (endBlockModel_cls_of_eqvGen he).symm

/-- **The move predicate of the class of `r`**, in closed form: a dart moves when neither it nor
its reverse has the class index of `r`. -/
theorem endBlockModel_movePred (r d : Model.diagram.toCombMap.Dart) :
    GL05b.movePred Model.diagram.toCombMap (GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r) d =
      (!decide (endBlockModel_cls d = endBlockModel_cls r) &&
        !decide (endBlockModel_cls (Model.diagram.toCombMap.alpha d) = endBlockModel_cls r)) := by
  rw [GL05b.movePred, endBlockModel_colour r d,
    endBlockModel_colour r (Model.diagram.toCombMap.alpha d)]

end GroupApproximation.Full.GL05c

#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_cls
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_cls_facePerm
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_cls_alpha
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_cls_cases
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_cls_step
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_cls_of_eqvGen
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_eqvGen_of_faceClass
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_not_walkKeep_14
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_eqvGen_14_15
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_eqvGen_of_cls
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_colour
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_movePred
