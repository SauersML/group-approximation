import GroupApproximation.GGT.VanKampen.ClosedWalkIslandModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellBlocks
import GroupApproximation.Meta.AxiomGuard

/-!
# A model test for the same-cell pocket value clause

`OsinLemma94SameCellPocketInput` (Osin, math/0411039v3, §9, proof of Lemma 9.4) takes a dart `d` of a
relator cell `i` whose reverse lies on cell `i`, oriented so that its start reaches the exterior
without crossing its edge.  It concludes that the cell word strictly between `d` and `α d` reads
`1`.  Its hypotheses also include least area, the `C`-condition and clause (b) of Lemma 9.7 below.
This module shows that the combinatorial clauses alone force nothing.

The map is ms-traces-2's `ClosedWalkIslandModel.M`: six darts, a loop `0/1` at `a = {0,1,2}`, a loop
`4/5` at `b = {3,4,5}` and a bridge `t = 2/3`.  Here the exterior is the monogon `[0]`, the island
`[4]` is a relator cell reading `b`, and the ring `[1,2,5,3]` around the bridge is a relator cell
reading `a⁻¹ t b⁻¹ t⁻¹`, so the bridge has cell `i` on both sides.

* `not_pocketValue`: at `d = 2` every combinatorial clause of `PocketValue` holds (`two_mem`,
  `faceOf_alpha_two`, `oriented_two`, `len_two`, `step_two`), and the pocket `[5]` reads `b⁻¹ ≠ 1`
  (`pocket_two_value`).  The island is a relator cell inside the pocket, so least area, the
  `C`-condition and the induction hypothesis carry the clause.
* `not_oriented_three`, `free_three` and `pocket_three_value`: at the reverse dart `d = 3` the
  orientation clause fails.  No relator cell other than the ring lies on the far side, and the
  pocket `[1]` still reads `a⁻¹ ≠ 1`, because that side holds the exterior.  So the orientation
  clause is load-bearing, for the input and for `BridgeComponent.listVal_pocket_eq_one`.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, through Osin's Lemma 9.4); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.SameCellPocketModel

open Equiv GroupApproximation.HullSC Embedded OsinUnboundSameCellBlocks ClosedWalkIslandModel

/-- The relator words: the ring `a⁻¹ t b⁻¹ t⁻¹` and the island `b`. -/
def pocketW : Set (List (RelLetter G Empty)) :=
  {[.base ga⁻¹, .base gt, .base gb⁻¹, .base gt⁻¹], [.base gb]}

/-- The island cell on `[4]`. -/
def cellIsland : RelatorCell M (face 0) pocketW where
  face := face 1
  face_ne_outer := (face_eq_iff 1 0).not.mpr (by decide)
  word := [.base gb]
  word_mem := Or.inr rfl
  conjugator := ga⁻¹ * gt
  reversed := false

/-- The ring cell on `[1,2,5,3]`, around the bridge. -/
def cellRing : RelatorCell M (face 0) pocketW where
  face := face 2
  face_ne_outer := (face_eq_iff 2 0).not.mpr (by decide)
  word := [.base ga⁻¹, .base gt, .base gb⁻¹, .base gt⁻¹]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

/-- **The model diagram**: exterior `[0]`, relator cells on the island `[4]` and the ring
`[1,2,5,3]`. -/
noncomputable def pocketDiagram : DiscDiagram pocketW where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 0
  faceBoundary := boundary
  relatorCells := [cellIsland, cellRing]
  relatorCell_faces_nodup := by
    change [face 1, face 2].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (face_eq_iff 1 2).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base gb] = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base ga⁻¹, .base gt, .base gb⁻¹, .base gt⁻¹] =
        (boundary (face 2)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact (hf rfl).elim
    · exact Or.inl ⟨cellIsland, by simp, rfl⟩
    · exact Or.inl ⟨cellRing, by simp, rfl⟩
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance (n : ℕ) : OfNat pocketDiagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 6) n)
instance : DecidableEq pocketDiagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 6))

/-- The index of the ring cell. -/
def ringIndex : Fin pocketDiagram.rCellCount := ⟨1, by show 1 < 2; decide⟩

theorem cell_ringIndex : cell pocketDiagram ringIndex = cellRing := rfl

theorem cellDarts_ringIndex : cellDarts pocketDiagram ringIndex = [1, 2, 5, 3] := by
  change (boundary (face 2)).darts = _
  rw [boundary_face_darts]
  rfl

/-! ## The dart `2`: every combinatorial clause holds, and the pocket reads `b⁻¹` -/

theorem two_mem : (2 : pocketDiagram.toCombMap.Dart) ∈ cellDarts pocketDiagram ringIndex := by
  rw [cellDarts_ringIndex]
  decide

theorem faceOf_alpha_two :
    pocketDiagram.toCombMap.faceOf (pocketDiagram.toCombMap.alpha 2) =
      (cell pocketDiagram ringIndex).face :=
  (faceOf_eq_face (alpha 2) 2).mpr (by decide)

theorem oriented_two :
    ∃ o : pocketDiagram.toCombMap.Dart, pocketDiagram.toCombMap.faceOf o = pocketDiagram.outerFace ∧
      Relation.EqvGen (AvoidEdgeStep pocketDiagram.toCombMap 2) 2 o :=
  ⟨0, (faceOf_eq_face 0 0).mpr rfl,
    .trans _ (1 : Fin 6) _ (.rel _ _ (Or.inl (by decide))) (.rel _ _ (Or.inl (by decide)))⟩

theorem len_two : 1 + 1 < (cellDarts pocketDiagram ringIndex).length := by
  rw [cellDarts_ringIndex]
  decide

theorem step_two :
    (pocketDiagram.toCombMap.facePerm ^ (1 + 1)) 2 = pocketDiagram.toCombMap.alpha 2 := by
  decide

theorem pocket_two_value :
    RelLetter.listVal (dartWord pocketDiagram
      ((List.range 1).map fun t => (pocketDiagram.toCombMap.facePerm ^ (t + 1)) 2)) = gb⁻¹ := by
  decide

/-- **The combinatorial clauses do not give the pocket value.** -/
theorem not_pocketValue : ¬ PocketValue pocketDiagram := by
  intro h
  have hv := h ringIndex 2 two_mem faceOf_alpha_two oriented_two 1 len_two step_two
  rw [pocket_two_value] at hv
  exact absurd hv (by decide)

/-! ## The dart `3`: the orientation clause fails, and the cell-free pocket reads `a⁻¹` -/

/-- Moves that avoid the bridge keep the vertex. -/
theorem vertexClass_of_avoid :
    ∀ x y : Fin 6, AvoidEdgeStep M 3 x y → vertexClass x = vertexClass y := by
  unfold AvoidEdgeStep
  decide

theorem vertexClass_of_eqvGen {x y : Fin 6} (h : Relation.EqvGen (AvoidEdgeStep M 3) x y) :
    vertexClass x = vertexClass y := by
  induction h with
  | rel x y h => exact vertexClass_of_avoid x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The reverse dart is not oriented toward the exterior.** -/
theorem not_oriented_three :
    ¬ ∃ o : pocketDiagram.toCombMap.Dart, pocketDiagram.toCombMap.faceOf o = pocketDiagram.outerFace ∧
      Relation.EqvGen (AvoidEdgeStep pocketDiagram.toCombMap 3) 3 o := by
  rintro ⟨o, ho, hch⟩
  have hcls : vertexClass 3 = vertexClass o := vertexClass_of_eqvGen hch
  have hface : faceClass o = 0 := (faceOf_eq_face o 0).mp ho
  have hall : ∀ o : Fin 6, faceClass o = 0 → vertexClass 3 = vertexClass o → False := by decide
  exact hall o hface hcls

/-- **No relator cell other than the ring lies on the far side of `3`.** -/
theorem free_three :
    ∀ C ∈ pocketDiagram.relatorCells, C.face ≠ pocketDiagram.toCombMap.faceOf 3 →
      ∀ x, pocketDiagram.toCombMap.faceOf x = C.face →
        ¬ Relation.EqvGen (AvoidEdgeStep pocketDiagram.toCombMap 3) x
          (pocketDiagram.toCombMap.alpha 3) := by
  intro C hC hne x hx hch
  have hcls : vertexClass x = vertexClass (alpha 3) := vertexClass_of_eqvGen hch
  rcases List.mem_cons.mp hC with rfl | hC
  · have hx' : faceClass x = 1 := (faceOf_eq_face x 1).mp hx
    have hall : ∀ x : Fin 6, faceClass x = 1 → vertexClass x = vertexClass (alpha 3) → False := by
      decide
    exact hall x hx' hcls
  · obtain rfl := List.mem_singleton.mp hC
    exact hne ((faceOf_eq_face 3 2).mpr rfl).symm

theorem step_three :
    (pocketDiagram.toCombMap.facePerm ^ (1 + 1)) 3 = pocketDiagram.toCombMap.alpha 3 := by
  decide

theorem pocket_three_value :
    RelLetter.listVal (dartWord pocketDiagram
      ((List.range 1).map fun t => (pocketDiagram.toCombMap.facePerm ^ (t + 1)) 3)) = ga⁻¹ := by
  decide

theorem ga_inv_ne_one : ga⁻¹ ≠ 1 := by decide

end GroupApproximation.GGT.VanKampen.SameCellPocketModel

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketModel.not_pocketValue
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketModel.not_oriented_three
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketModel.free_three
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketModel.step_three
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketModel.pocket_three_value
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketModel.ga_inv_ne_one
