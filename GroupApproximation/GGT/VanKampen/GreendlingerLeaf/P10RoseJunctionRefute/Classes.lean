import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Premises
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Move
import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The walk classes of the 24-dart pocket

Lane gl-p10-51.

The walk `[0,2,16,4,6,18,8,20,10,12,22]` of `roseJunctionRefute_pK` keeps every edge but
`{14,15}`.  So the face classes of `FaceClassStep (walkKeep …)` are
`{0}`, `{1,3,5,7,9,11,13,14,15,17,19,21,23}`, `{2,6,16,18}`, `{4}`, `{8,12,20,22}` and `{10}`,
numbered `0, …, 5` by `roseJunctionRefute_cid` (`roseJunctionRefute_eqvGen_iff`).

Proof route: `cid` is constant along a step (`decide`), and every dart is joined to the listed
representative of its class by explicit steps.  The colour `regionColour … r` is then
`decide (cid r = cid x)`, the moved darts are `roseJunctionRefute_keptTab (cid r)`, and the flip
of the faces `S` and `K₀` is read off by `P10Rose.FilterMove.mem_flipFaces_iff`.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

/-- The walk class of each dart. -/
def roseJunctionRefute_cid : Fin 24 → Fin 6 :=
  ![0, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1]

/-- A representative of each walk class. -/
def roseJunctionRefute_rep : Fin 6 → Fin 24 := ![0, 1, 2, 4, 8, 10]

/-- The darts of the edges of the walk. -/
def roseJunctionRefute_keepB : Fin 24 → Bool :=
  ![true, true, true, true, true, true, true, true, true, true, true, true, true, true, false,
    false, true, true, true, true, true, true, true, true]

/-- The moved-dart predicate of the class `c`. -/
def roseJunctionRefute_keptTab (c : Fin 6) (x : roseJunctionRefute_X.toCombMap.Dart) : Bool :=
  !decide (c = roseJunctionRefute_cid x) &&
    !decide (c = roseJunctionRefute_cid (roseJunctionRefute_X.toCombMap.alpha x))

/-- The darts on the edges of the pocket walk. -/
abbrev roseJunctionRefute_keep : roseJunctionRefute_X.toCombMap.Dart → Prop :=
  SimpleClosedWalkSides.walkKeep roseJunctionRefute_X.toCombMap
    roseJunctionRefute_pK.boundary.cycle

/-- One step inside a walk class. -/
abbrev roseJunctionRefute_stepRel :
    roseJunctionRefute_X.toCombMap.Dart → roseJunctionRefute_X.toCombMap.Dart → Prop :=
  CombMap.FaceClassStep roseJunctionRefute_X.toCombMap roseJunctionRefute_keep

theorem roseJunctionRefute_keep_iff (x : roseJunctionRefute_X.toCombMap.Dart) :
    roseJunctionRefute_keep x ↔ roseJunctionRefute_keepB x = true := by
  unfold roseJunctionRefute_keep SimpleClosedWalkSides.walkKeep
  revert x
  decide

theorem roseJunctionRefute_notKeep14 : ¬roseJunctionRefute_keep 14 := fun h =>
  absurd ((roseJunctionRefute_keep_iff 14).mp h) (by decide)

theorem roseJunctionRefute_cid_facePerm : ∀ x : roseJunctionRefute_X.toCombMap.Dart,
    roseJunctionRefute_cid (roseJunctionRefute_X.toCombMap.facePerm x) =
      roseJunctionRefute_cid x := by
  decide

theorem roseJunctionRefute_cid_alpha_aux : ∀ x : roseJunctionRefute_X.toCombMap.Dart,
    roseJunctionRefute_keepB x = false →
      roseJunctionRefute_cid (roseJunctionRefute_X.toCombMap.alpha x) =
        roseJunctionRefute_cid x := by
  decide

theorem roseJunctionRefute_cid_alpha (x : roseJunctionRefute_X.toCombMap.Dart)
    (hk : ¬roseJunctionRefute_keep x) :
    roseJunctionRefute_cid (roseJunctionRefute_X.toCombMap.alpha x) =
      roseJunctionRefute_cid x :=
  roseJunctionRefute_cid_alpha_aux x
    (Bool.eq_false_iff.mpr fun h => hk ((roseJunctionRefute_keep_iff x).mpr h))

theorem roseJunctionRefute_step_cid (x y : roseJunctionRefute_X.toCombMap.Dart)
    (h : roseJunctionRefute_stepRel x y) :
    roseJunctionRefute_cid x = roseJunctionRefute_cid y := by
  rcases h with h | ⟨hk, h⟩
  · rw [h, roseJunctionRefute_cid_facePerm]
  · rw [h, roseJunctionRefute_cid_alpha x hk]

/-- Every dart is joined to the representative of its class. -/
theorem roseJunctionRefute_from_rep (x : Fin 24) :
    Relation.EqvGen roseJunctionRefute_stepRel
      (roseJunctionRefute_rep (roseJunctionRefute_cid x)) x := by
  have f {a b : roseJunctionRefute_X.toCombMap.Dart}
      (h : roseJunctionRefute_X.toCombMap.facePerm a = b) :
      Relation.EqvGen roseJunctionRefute_stepRel a b :=
    .rel _ _ (Or.inl h.symm)
  have t {a b c : roseJunctionRefute_X.toCombMap.Dart}
      (h1 : Relation.EqvGen roseJunctionRefute_stepRel a b)
      (h2 : Relation.EqvGen roseJunctionRefute_stepRel b c) :
      Relation.EqvGen roseJunctionRefute_stepRel a c :=
    .trans _ _ _ h1 h2
  have h19 : Relation.EqvGen roseJunctionRefute_stepRel 1 19 := f (by decide)
  have h7 : Relation.EqvGen roseJunctionRefute_stepRel 1 7 := t h19 (f (by decide))
  have h5 : Relation.EqvGen roseJunctionRefute_stepRel 1 5 := t h7 (f (by decide))
  have h17 : Relation.EqvGen roseJunctionRefute_stepRel 1 17 := t h5 (f (by decide))
  have h3 : Relation.EqvGen roseJunctionRefute_stepRel 1 3 := t h17 (f (by decide))
  have h14 : Relation.EqvGen roseJunctionRefute_stepRel 1 14 := t h3 (f (by decide))
  have h15 : Relation.EqvGen roseJunctionRefute_stepRel 1 15 :=
    t h14 (.rel _ _ (Or.inr ⟨roseJunctionRefute_notKeep14, by decide⟩))
  have h23 : Relation.EqvGen roseJunctionRefute_stepRel 1 23 := t h15 (f (by decide))
  have h13 : Relation.EqvGen roseJunctionRefute_stepRel 1 13 := t h23 (f (by decide))
  have h11 : Relation.EqvGen roseJunctionRefute_stepRel 1 11 := t h13 (f (by decide))
  have h21 : Relation.EqvGen roseJunctionRefute_stepRel 1 21 := t h11 (f (by decide))
  have h9 : Relation.EqvGen roseJunctionRefute_stepRel 1 9 := t h21 (f (by decide))
  have h16 : Relation.EqvGen roseJunctionRefute_stepRel 2 16 := f (by decide)
  have h6 : Relation.EqvGen roseJunctionRefute_stepRel 2 6 := t h16 (f (by decide))
  have h18 : Relation.EqvGen roseJunctionRefute_stepRel 2 18 := t h6 (f (by decide))
  have h20 : Relation.EqvGen roseJunctionRefute_stepRel 8 20 := f (by decide)
  have h12 : Relation.EqvGen roseJunctionRefute_stepRel 8 12 := t h20 (f (by decide))
  have h22 : Relation.EqvGen roseJunctionRefute_stepRel 8 22 := t h12 (f (by decide))
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
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23

/-- **The walk classes are the fibres of `cid`.** -/
theorem roseJunctionRefute_eqvGen_iff (r x : roseJunctionRefute_X.toCombMap.Dart) :
    Relation.EqvGen roseJunctionRefute_stepRel r x ↔
      roseJunctionRefute_cid r = roseJunctionRefute_cid x := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact roseJunctionRefute_step_cid a b hab
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    have h1 := roseJunctionRefute_from_rep r
    have h2 := roseJunctionRefute_from_rep x
    rw [h] at h1
    exact .trans _ _ _ (.symm _ _ h1) h2

theorem roseJunctionRefute_colour_eq (r x : roseJunctionRefute_X.toCombMap.Dart) :
    P10Rose.SubArcMove.regionColour roseJunctionRefute_X.toCombMap roseJunctionRefute_keep r x =
      decide (roseJunctionRefute_cid r = roseJunctionRefute_cid x) :=
  P10Rose.SubArcMove.bool_eq_of_iff
    ((P10Rose.SubArcMove.regionColour_eq_true_iff roseJunctionRefute_X.toCombMap
      roseJunctionRefute_keep r x).trans
      ((roseJunctionRefute_eqvGen_iff r x).trans decide_eq_true_iff.symm))

/-- **The moved darts of the class `c`** are the darts `keptTab c`. -/
theorem roseJunctionRefute_move_eq (r : roseJunctionRefute_X.toCombMap.Dart) (c : Fin 6)
    (hc : roseJunctionRefute_cid r = c) :
    P10Rose.FilterMove.movePred roseJunctionRefute_X.toCombMap
      (P10Rose.SubArcMove.regionColour roseJunctionRefute_X.toCombMap roseJunctionRefute_keep r) =
      roseJunctionRefute_keptTab c := by
  funext x
  unfold P10Rose.FilterMove.movePred
  rw [roseJunctionRefute_colour_eq, roseJunctionRefute_colour_eq, hc]
  rfl

/-- The flip of the face of a dart `x`. -/
theorem roseJunctionRefute_flip (r x : roseJunctionRefute_X.toCombMap.Dart) :
    roseJunctionRefute_X.toCombMap.faceOf x ∈ P10Rose.FilterMove.flipFaces
      roseJunctionRefute_X.toCombMap roseJunctionRefute_pK.faces
      (P10Rose.SubArcMove.regionColour roseJunctionRefute_X.toCombMap roseJunctionRefute_keep r) ↔
      (roseJunctionRefute_faceIn (roseJunctionRefute_faceClass x) = true ↔
        decide (roseJunctionRefute_cid r = roseJunctionRefute_cid x) = false) := by
  rw [P10Rose.FilterMove.mem_flipFaces_iff
    (P10Rose.SubArcMove.regionColour_step _ roseJunctionRefute_keep r) x,
    roseJunctionRefute_colour_eq]
  change (roseJunctionRefute_M.faceOf x ∈ roseJunctionRefute_pFaces ↔ _) ↔ _
  rw [roseJunctionRefute_faceOf_eq_face', roseJunctionRefute_faceMem]

/-- **The source cell `S` flips exactly for the class `1`.** -/
theorem roseJunctionRefute_flipS (r : roseJunctionRefute_X.toCombMap.Dart) :
    (Embedded.cell roseJunctionRefute_X roseJunctionRefute_iS).face ∈
      P10Rose.FilterMove.flipFaces roseJunctionRefute_X.toCombMap roseJunctionRefute_pK.faces
      (P10Rose.SubArcMove.regionColour roseJunctionRefute_X.toCombMap roseJunctionRefute_keep r) ↔
      roseJunctionRefute_cid r = 1 := by
  have h := roseJunctionRefute_flip r 19
  have h19 : roseJunctionRefute_faceIn
      (roseJunctionRefute_faceClass (19 : roseJunctionRefute_X.toCombMap.Dart)) = false ∧
      roseJunctionRefute_cid (19 : roseJunctionRefute_X.toCombMap.Dart) = 1 := by decide
  rw [h19.1, h19.2] at h
  refine h.trans ?_
  by_cases hc : roseJunctionRefute_cid r = 1 <;> simp [hc]

/-- **The kept cell `K₀` flips exactly off the class `0`.** -/
theorem roseJunctionRefute_flipK (r : roseJunctionRefute_X.toCombMap.Dart) :
    (Embedded.cell roseJunctionRefute_X roseJunctionRefute_iK0).face ∈
      P10Rose.FilterMove.flipFaces roseJunctionRefute_X.toCombMap roseJunctionRefute_pK.faces
      (P10Rose.SubArcMove.regionColour roseJunctionRefute_X.toCombMap roseJunctionRefute_keep r) ↔
      roseJunctionRefute_cid r ≠ 0 := by
  have h := roseJunctionRefute_flip r 0
  have h0 : roseJunctionRefute_faceIn
      (roseJunctionRefute_faceClass (0 : roseJunctionRefute_X.toCombMap.Dart)) = true ∧
      roseJunctionRefute_cid (0 : roseJunctionRefute_X.toCombMap.Dart) = 0 := by decide
  rw [h0.1, h0.2] at h
  refine h.trans ?_
  by_cases hc : roseJunctionRefute_cid r = 0 <;> simp [hc]

theorem roseJunctionRefute_cell_cases : ∀ i : Fin roseJunctionRefute_X.rCellCount,
    i = roseJunctionRefute_iS ∨ i = roseJunctionRefute_iK0
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl
  | ⟨k + 2, hk⟩ => absurd hk (Nat.not_lt.mpr (Nat.le_add_left 2 k))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_cid
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_rep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_keepB
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_keptTab
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_stepRel
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_keep_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_notKeep14
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_cid_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_cid_alpha_aux
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_cid_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_step_cid
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_from_rep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_eqvGen_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_colour_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_move_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_flip
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_flipS
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_flipK
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_cell_cases
