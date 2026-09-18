import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickClsDiagram
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClassChoice
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalResidual
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Move
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCells
import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The walk classes of the counterexample pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-40.

The walk `[0,2,4,6,8,10,12]` of `ExtremalJordanPickClsModel.pK` keeps every edge but `{14,15}`.
So the face classes are `{0}`, `{1,3,5,7,9,11,13,14,15}`, `{2,6}`, `{4}`, `{8,12}` and `{10}`,
numbered `0, …, 5` by `cid` (`eqvGen_iff`).

* `no_class`: no dart `r` meets both `ExtremalClassChoice` and `ExtremalClassStretches`.
  - The class `{0}` meets no relator cell of the pocket other than `K₀ = [0]` itself.
  - The class `1` meets the exterior face and keeps no dart of the target arc.
  - The classes `{2,6}` and `{8,12}` leave stretches with unlinked ends.
  - The class `{4}` leaves a stretch within the source arc, and `{10}` one within the target arc.
* `class_two`: the class `{2,6}` of the walk dart `2` holds no relator cell, so
  `ExtremalJordanPickCellsClass` fails.

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel

/-- The walk class of each dart. -/
def cid : Fin 16 → Fin 6 := ![0, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5, 1, 4, 1, 1, 1]

/-- A representative of each walk class. -/
def rep : Fin 6 → Fin 16 := ![0, 1, 2, 4, 8, 10]

/-- The darts of the edges of the walk. -/
def keepB : Fin 16 → Bool :=
  ![true, true, true, true, true, true, true, true, true, true, true, true, true, true, false,
    false]

/-- The kept predicate of the class `c`. -/
def keptTab (c : Fin 6) (x : Fin 16) : Bool :=
  !decide (c = cid x) && !decide (c = cid (M.alpha x))

/-- One step inside a walk class. -/
abbrev stepRel : diagram.toCombMap.Dart → diagram.toCombMap.Dart → Prop :=
  CombMap.FaceClassStep diagram.toCombMap
    (SimpleClosedWalkSides.walkKeep diagram.toCombMap pK.boundary.cycle)

theorem keep_iff (x : diagram.toCombMap.Dart) :
    SimpleClosedWalkSides.walkKeep diagram.toCombMap pK.boundary.cycle x ↔ keepB x = true := by
  unfold SimpleClosedWalkSides.walkKeep
  revert x
  decide

theorem notKeep14 :
    ¬SimpleClosedWalkSides.walkKeep diagram.toCombMap pK.boundary.cycle 14 := fun h =>
  absurd ((keep_iff 14).mp h) (by decide)

theorem cid_facePerm :
    ∀ x : diagram.toCombMap.Dart, cid (diagram.toCombMap.facePerm x) = cid x := by
  decide

theorem cid_alpha_aux : ∀ x : diagram.toCombMap.Dart, keepB x = false →
    cid (diagram.toCombMap.alpha x) = cid x := by
  decide

theorem cid_alpha_of_not_keep (x : diagram.toCombMap.Dart)
    (hk : ¬SimpleClosedWalkSides.walkKeep diagram.toCombMap pK.boundary.cycle x) :
    cid (diagram.toCombMap.alpha x) = cid x :=
  cid_alpha_aux x (Bool.eq_false_iff.mpr fun h => hk ((keep_iff x).mpr h))

theorem step_cid (x y : diagram.toCombMap.Dart) (h : stepRel x y) : cid x = cid y := by
  rcases h with h | ⟨hk, h⟩
  · rw [h, cid_facePerm]
  · rw [h, cid_alpha_of_not_keep x hk]

/-- Every dart is joined to the representative of its class. -/
theorem from_rep (x : Fin 16) : Relation.EqvGen stepRel (rep (cid x)) x := by
  have f {a b : diagram.toCombMap.Dart} (h : diagram.toCombMap.facePerm a = b) :
      Relation.EqvGen stepRel a b :=
    .rel _ _ (Or.inl h.symm)
  have t {a b c : diagram.toCombMap.Dart} (h1 : Relation.EqvGen stepRel a b)
      (h2 : Relation.EqvGen stepRel b c) : Relation.EqvGen stepRel a c :=
    .trans _ _ _ h1 h2
  have h7 : Relation.EqvGen stepRel 1 7 := f (by decide)
  have h5 : Relation.EqvGen stepRel 1 5 := t h7 (f (by decide))
  have h3 : Relation.EqvGen stepRel 1 3 := t h5 (f (by decide))
  have h14 : Relation.EqvGen stepRel 1 14 := t h3 (f (by decide))
  have h15 : Relation.EqvGen stepRel 1 15 :=
    t h14 (.rel _ _ (Or.inr ⟨notKeep14, by decide⟩))
  have h13 : Relation.EqvGen stepRel 1 13 := t h15 (f (by decide))
  have h11 : Relation.EqvGen stepRel 1 11 := t h13 (f (by decide))
  have h9 : Relation.EqvGen stepRel 1 9 := t h11 (f (by decide))
  have h6 : Relation.EqvGen stepRel 2 6 := f (by decide)
  have h12 : Relation.EqvGen stepRel 8 12 := f (by decide)
  fin_cases x
  · exact .refl _
  · exact .refl _
  · exact .refl _
  · exact h3
  · exact .refl _
  · exact h5
  · exact h6
  · exact h7
  · exact .refl _
  · exact h9
  · exact .refl _
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- **The walk classes are the fibres of `cid`.** -/
theorem eqvGen_iff (r x : diagram.toCombMap.Dart) :
    Relation.EqvGen (CombMap.FaceClassStep diagram.toCombMap
      (SimpleClosedWalkSides.walkKeep diagram.toCombMap pK.boundary.cycle)) r x ↔
      cid r = cid x := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact step_cid a b hab
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    have h1 := from_rep r
    have h2 := from_rep x
    rw [h] at h1
    exact .trans _ _ _ (.symm _ _ h1) h2

/-! ## Colours and kept darts -/

theorem colour_eq (r x : diagram.toCombMap.Dart) :
    GreendlingerLeaf.P10Rose.SubArcMove.regionColour diagram.toCombMap
      (SimpleClosedWalkSides.walkKeep diagram.toCombMap pK.boundary.cycle) r x =
      decide (cid r = cid x) :=
  GreendlingerLeaf.P10Rose.SubArcMove.bool_eq_of_iff
    ((GreendlingerLeaf.P10Rose.SubArcMove.regionColour_eq_true_iff diagram.toCombMap
      (SimpleClosedWalkSides.walkKeep diagram.toCombMap pK.boundary.cycle) r x).trans
      ((eqvGen_iff r x).trans decide_eq_true_iff.symm))

theorem kept_eq (r e : diagram.toCombMap.Dart) :
    GreendlingerLeaf.P10ExtremalResidual.keptPred pK r e =
      (!decide (cid r = cid e) && !decide (cid r = cid (diagram.toCombMap.alpha e))) := by
  unfold GreendlingerLeaf.P10ExtremalResidual.keptPred
  unfold GreendlingerLeaf.P10Rose.FilterMove.movePred
  rw [colour_eq, colour_eq]

theorem kept_at (r e : diagram.toCombMap.Dart) (c : Fin 6) (hc : cid r = c) :
    GreendlingerLeaf.P10ExtremalResidual.keptPred pK r e = keptTab c e := by
  subst hc
  exact kept_eq r e

theorem kept_single (r x b : diagram.toCombMap.Dart) (c : Fin 6) (hc : cid r = c)
    (hb : keptTab c b = false) (hx : x ∈ [b]) :
    GreendlingerLeaf.P10ExtremalResidual.keptPred pK r x = false := by
  rw [List.mem_singleton] at hx
  subst hx
  exact (kept_at r _ c hc).trans hb

theorem cell_cases : ∀ i : Fin diagram.rCellCount, i = iS ∨ i = iK0
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl
  | ⟨k + 2, hk⟩ => absurd hk (Nat.not_lt.mpr (Nat.le_add_left 2 k))

/-! ## No class is extremal -/

/-- **No dart spans an extremal class** of the pocket `pK`. -/
theorem no_class (r : diagram.toCombMap.Dart)
    (hch : GreendlingerLeaf.P10ExtremalRegion.ExtremalClassChoice pK r)
    (hst : GreendlingerLeaf.P10ExtremalRegion.ExtremalClassStretches pK r) : False := by
  obtain ⟨hT, -, kept, hkf, hkx⟩ := hch
  have hsix : ∀ c : Fin 6, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by decide
  rcases hsix (cid r) with hc | hc | hc | hc | hc | hc
  · rcases cell_cases kept with rfl | rfl
    · exact absurd ((face_mem_iff 1).mp hkf) (by decide)
    · exact hkx 0 ((faceOf_eq_face 0 0).mpr (by decide))
        ((eqvGen_iff r 0).mpr (hc.trans (by decide)))
  · rcases hT with ⟨e, he, hke⟩ | hT
    · rw [pK_target] at he
      have hno : ∀ e ∈ ([8, 10, 12] : List diagram.toCombMap.Dart), keptTab 1 e ≠ true := by
        decide
      exact hno e he ((kept_at r e 1 hc).symm.trans hke)
    · exact hT 9 ((faceOf_eq_face 9 5).mpr (by decide))
        ((eqvGen_iff r 9).mpr (hc.trans (by decide)))
  · have h := hst [] 0 [2] 4 [6, 8, 10, 12] (by decide) ((kept_at r 0 2 hc).trans (by decide))
      ((kept_at r 4 2 hc).trans (by decide)) (fun x hx => kept_single r x 2 2 hc (by decide) hx)
      (List.cons_ne_nil _ _)
    exact absurd ((vClass_iff _ _).mp h.1) (by decide)
  · have h := hst [0] 2 [4] 6 [8, 10, 12] (by decide) ((kept_at r 2 3 hc).trans (by decide))
      ((kept_at r 6 3 hc).trans (by decide)) (fun x hx => kept_single r x 4 3 hc (by decide) hx)
      (List.cons_ne_nil _ _)
    exact h.2.2 (by rw [pK_invSrc]; decide)
  · have h := hst [0, 2, 4] 6 [8] 10 [12] (by decide) ((kept_at r 6 4 hc).trans (by decide))
      ((kept_at r 10 4 hc).trans (by decide)) (fun x hx => kept_single r x 8 4 hc (by decide) hx)
      (List.cons_ne_nil _ _)
    exact absurd ((vClass_iff _ _).mp h.1) (by decide)
  · have h := hst [0, 2, 4, 6] 8 [10] 12 [] (by decide) ((kept_at r 8 5 hc).trans (by decide))
      ((kept_at r 12 5 hc).trans (by decide))
      (fun x hx => kept_single r x 10 5 hc (by decide) hx) (List.cons_ne_nil _ _)
    exact h.2.1 (by rw [pK_target]; decide)

/-- **The walk class of `2` holds no relator cell.** -/
theorem class_two (h : GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCellsClass pK) :
    False := by
  obtain ⟨i, hi, x, hx, hrx⟩ := h 2 (by decide)
  have hc := (eqvGen_iff 2 x).mp hrx
  rcases cell_cases i with rfl | rfl
  · exact absurd ((face_mem_iff 1).mp hi) (by decide)
  · exact (by decide : ∀ y : Fin 16, faceClass y = 0 → cid 2 ≠ cid y) x
      ((faceOf_eq_face x 0).mp hx) hc

end GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel

#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cid
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.rep
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.keepB
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.keptTab
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.stepRel
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.keep_iff
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.notKeep14
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cid_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cid_alpha_aux
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cid_alpha_of_not_keep
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.step_cid
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.from_rep
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.eqvGen_iff
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.colour_eq
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.kept_eq
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.kept_at
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.kept_single
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cell_cases
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.no_class
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.class_two
