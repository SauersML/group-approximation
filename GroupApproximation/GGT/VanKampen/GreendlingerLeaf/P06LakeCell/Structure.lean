import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): the exterior class touches only the sides

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  In the lakes surgery of
`Piece06.CellRoseLakesSurgeryBelowStatement`, let `K` be a cell pocket face set with boundary cycle
`s₁ t̄₁ s₂ t̄₂`, let `E₀ = ExteriorComponent.component X.toCombMap K.faces X.outerFace` be the
exterior piece, and let `F' = ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace` be the
face set with its lakes filled.  Case (d) is the case `hall`: every relator cell lies off `E₀`.

Mathematical proof (every step is elementary).

* `cells_mem_absorbed_of_all`: `Π_i` and `Π_j` are relator cells (`cell_mem`), so under `hall`
  they are off `E₀`, that is in `F'` (`mem_absorbed_iff`).
* `faceOf_alpha_of_mem_invFirstArc` / `_invSecondArc`: a dart `d = α e` of `t̄₁` has
  `e ∈ t₁ ⊆ ∂Π_i`, so the face across `d` is `faceOf (α (α e)) = faceOf e = Π_i`.
* `boundaryDart_absorbed_mem_sides`: a boundary dart `d` of `F'` is a boundary dart of `K.faces`
  whose far face lies in `E₀` (`isBoundaryDart_absorbed_iff`).  So `d` is on the boundary cycle,
  which is `s₁ ++ t̄₁ ++ s₂ ++ t̄₂`.  If `d ∈ t̄₁`, its far face is `Π_i`, which is off `E₀` under
  `hall`: contradiction.  The same holds for `t̄₂` and `Π_j`.  Hence `d ∈ s₁ ∨ d ∈ s₂`.
* `absorbed_boundary_length_le`: the boundary darts of `F'` form a subset of
  `s₁.toFinset ∪ s₂.toFinset`, whose cardinality is at most `|s₁| + |s₂| ≤ ε + ε`.

This is exact infrastructure for lanes gl-p06-10..13; it needs no interface of another lane
(the LakeFree predicate of gl-p06-05 is not used).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded Surgery.MapCollapse

section Structure

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The face across a dart of `t̄₁` is `Π_i`.** -/
theorem faceOf_alpha_of_mem_invFirstArc (K : CellPocketFaceSet D eps X i j)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.firstArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X i).face := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary (cell X i).face).mem_iff e).mp
    (K.firstArc.mem_cycle_of_mem_darts (List.mem_reverse.mp he))

/-- **The face across a dart of `t̄₂` is `Π_j`.** -/
theorem faceOf_alpha_of_mem_invSecondArc (K : CellPocketFaceSet D eps X i j)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.secondArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X j).face := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary (cell X j).face).mem_iff e).mp
    (K.secondArc.mem_cycle_of_mem_darts (List.mem_reverse.mp he))

/-- **Case (d): both cells lie in the filled face set.**  When no relator cell lies in the
exterior piece, `Π_i` and `Π_j` lie in `F'`. -/
theorem cells_mem_absorbed_of_all (K : CellPocketFaceSet D eps X i j)
    (hall : ∀ C ∈ X.relatorCells,
      C.face ∉ ExteriorComponent.component X.toCombMap K.faces X.outerFace) :
    (cell X i).face ∈ ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace ∧
      (cell X j).face ∈ ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace :=
  ⟨ExteriorComponent.mem_absorbed_iff.mpr (hall (cell X i) (cell_mem X i)),
    ExteriorComponent.mem_absorbed_iff.mpr (hall (cell X j) (cell_mem X j))⟩

/-- **Case (d): the exterior piece touches only the sides.**  When no relator cell lies in the
exterior piece, every boundary dart of the filled face set `F'` is a dart of `s₁` or of `s₂`. -/
theorem boundaryDart_absorbed_mem_sides (K : CellPocketFaceSet D eps X i j)
    (hall : ∀ C ∈ X.relatorCells,
      C.face ∉ ExteriorComponent.component X.toCombMap K.faces X.outerFace) :
    ∀ d, Surgery.MapCollapse.IsBoundaryDart X.toCombMap
        (ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace) d →
      d ∈ K.firstSide ∨ d ∈ K.secondSide := by
  intro d hd
  obtain ⟨hb, hα⟩ :=
    (ExteriorComponent.isBoundaryDart_absorbed_iff K.outerFace_not_mem d).mp hd
  have hmem : d ∈ K.boundary.cycle := (K.boundary.cycle_mem_iff d).mpr hb
  rw [K.decomposition] at hmem
  rcases List.mem_append.mp hmem with h | h₄
  · rcases List.mem_append.mp h with h | h₃
    · rcases List.mem_append.mp h with h₁ | h₂
      · exact Or.inl h₁
      · rw [faceOf_alpha_of_mem_invFirstArc K h₂] at hα
        exact (hall (cell X i) (cell_mem X i) hα).elim
    · exact Or.inr h₃
  · rw [faceOf_alpha_of_mem_invSecondArc K h₄] at hα
    exact (hall (cell X j) (cell_mem X j) hα).elim

/-- **Case (d): the filled face set has boundary length at most `2ε`.**  When no relator cell lies
in the exterior piece, the boundary darts of `F'` number at most `ε + ε`. -/
theorem absorbed_boundary_length_le (K : CellPocketFaceSet D eps X i j)
    (hall : ∀ C ∈ X.relatorCells,
      C.face ∉ ExteriorComponent.component X.toCombMap K.faces X.outerFace) :
    (Embedded.boundaryDarts X
      (ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace)).card ≤ eps + eps := by
  classical
  have hsub : Embedded.boundaryDarts X
      (ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace) ⊆
        K.firstSide.toFinset ∪ K.secondSide.toFinset := by
    intro d hd
    have hb := (Embedded.mem_boundaryDarts_iff X
      (ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace) d).mp hd
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
    exact boundaryDart_absorbed_mem_sides K hall d hb
  calc (Embedded.boundaryDarts X
        (ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace)).card
      ≤ (K.firstSide.toFinset ∪ K.secondSide.toFinset).card := Finset.card_le_card hsub
    _ ≤ K.firstSide.toFinset.card + K.secondSide.toFinset.card := Finset.card_union_le _ _
    _ ≤ K.firstSide.length + K.secondSide.length :=
      Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
    _ ≤ eps + eps := Nat.add_le_add K.firstSide_length_le K.secondSide_length_le

end Structure

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.faceOf_alpha_of_mem_invFirstArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.faceOf_alpha_of_mem_invSecondArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.cells_mem_absorbed_of_all
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.boundaryDart_absorbed_mem_sides
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.absorbed_boundary_length_le
