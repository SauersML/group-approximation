import GroupApproximation.GGT.VanKampen.GEdgeSubdivision
import GroupApproximation.GGT.VanKampen.CombMapSubdivisionExpansion
import GroupApproximation.GGT.VanKampen.DiscExpansion

/-! # Full expansion and iteration data for the actual G-edge subdivision -/

namespace GroupApproximation.GGT.VanKampen.GEdgeSubdivision

open HullSC HullSC.Lemma44OrientedRelatorDiagram EdgeSubdivision
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (a : Delta.toCombMap.Dart)
  (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
  (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
  (left right : RelLetter G Lambda)
  (hfactor : (Delta.label a).val = left.val * right.val)

noncomputable def expansion : DiscExpansion Delta (diagram Delta a houter hcells left right hfactor) where
  toDartExpansion := dartExpansion Delta.toCombMap a
  faceEquiv := keep Delta a
  boundary_darts := allBoundary_darts Delta.toCombMap a Delta.faceBoundary
  outerFace_eq := rfl
  outerWord_eq := boundaryWord_eq Delta a houter hcells left right hfactor
  cells := orderedCells Delta a houter hcells left right hfactor
  cellFaces_eq := by
    change (Delta.relatorCells.map (cell Delta a)).map RelatorCell.face = _
    rw [List.map_map, List.map_map]
    rfl

include houter in
theorem remaining_outer :
    (map Delta a).faceOf (embed Delta.toCombMap a) ≠ keep Delta a Delta.outerFace ∧
    (map Delta a).faceOf ((map Delta a).alpha (embed Delta.toCombMap a)) ≠ keep Delta a Delta.outerFace := by
  constructor
  · intro h
    exact houter.1 ((faceEquiv_embed Delta.toCombMap a a).symm.trans
      ((congrArg (faceEquiv Delta.toCombMap a) h).trans
        ((faceEquiv Delta.toCombMap a).apply_symm_apply Delta.outerFace)))
  · intro h
    exact houter.2 ((faceEquiv_embed Delta.toCombMap a (Delta.toCombMap.alpha a)).symm.trans
      ((congrArg (faceEquiv Delta.toCombMap a) h).trans
        ((faceEquiv Delta.toCombMap a).apply_symm_apply Delta.outerFace)))

theorem remaining_cells :
    ∀ C ∈ (diagram Delta a houter hcells left right hfactor).relatorCells,
      (map Delta a).faceOf (embed Delta.toCombMap a) ≠ C.face ∧
      (map Delta a).faceOf ((map Delta a).alpha (embed Delta.toCombMap a)) ≠ C.face := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  constructor
  · intro h
    exact (hcells C₀ hC₀).1 ((faceEquiv_embed Delta.toCombMap a a).symm.trans
      ((congrArg (faceEquiv Delta.toCombMap a) h).trans
        ((faceEquiv Delta.toCombMap a).apply_symm_apply C₀.face)))
  · intro h
    exact (hcells C₀ hC₀).2 ((faceEquiv_embed Delta.toCombMap a (Delta.toCombMap.alpha a)).symm.trans
      ((congrArg (faceEquiv Delta.toCombMap a) h).trans
        ((faceEquiv Delta.toCombMap a).apply_symm_apply C₀.face)))

theorem remaining_label :
    (diagram Delta a houter hcells left right hfactor).label (embed Delta.toCombMap a) = right := by
  classical
  change subdivideLabel Delta.toCombMap a Delta.label left right (embed Delta.toCombMap a) = right
  simp [subdivideLabel, embed, EdgeInsertion.embed]

theorem label_away_remaining (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a → D.IsLetter (Delta.label d))
    (hleft : D.IsLetter left) (d : (map Delta a).Dart)
    (ha : d ≠ embed Delta.toCombMap a)
    (hb : d ≠ (map Delta a).alpha (embed Delta.toCombMap a)) :
    D.IsLetter ((diagram Delta a houter hcells left right hfactor).label d) := by
  classical
  change EdgeSubdivision.Dart Delta.toCombMap at d
  rcases d with _ | (_ | d)
  · exact hleft
  · exact isLetter_relWordInv D hsymm hleft
  · have hda : d ≠ a := fun h => ha (congrArg (embed Delta.toCombMap) h)
    have hdb : d ≠ Delta.toCombMap.alpha a := fun h => hb (congrArg (embed Delta.toCombMap) h)
    change D.IsLetter (subdivideLabel Delta.toCombMap a Delta.label left right (embed Delta.toCombMap d))
    simp only [subdivideLabel, embed, EdgeInsertion.embed]
    rw [if_neg hda, if_neg hdb]
    exact hlabel d hda hdb

end GroupApproximation.GGT.VanKampen.GEdgeSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.expansion
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.remaining_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.label_away_remaining
