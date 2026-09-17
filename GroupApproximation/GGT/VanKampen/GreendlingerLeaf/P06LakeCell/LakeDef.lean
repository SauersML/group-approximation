import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, case (d): the lake holding an enclosed cell

Lane `gl-p06-10` of `lanes/carto-gl-p06.md` (Route C, infrastructure for lanes 11–13 on
`Piece06.CellRoseLakesSurgeryBelowStatement`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

## Objects

Let `K : CellPocketFaceSet D eps X i j` and let `k` be a relator cell whose face `Π_k` is off
`K.faces`.  The **lake of `Π_k`** is the piece of `Π_k` in the complement of `K.faces`:
`lakeOf K k = ExteriorComponent.component X.toCombMap K.faces (cell X k).face`, the faces reached
from `Π_k` by moving around faces and crossing edges off the boundary of `K.faces`.

## Truth checks (paper)

1. `Π_k ∈ lakeOf K k` (`ExteriorComponent.self_mem_component`), and `lakeOf K k` is disjoint from
   `K.faces` when `Π_k ∉ K.faces` (`ExteriorComponent.not_mem_of_mem_component`).  So the kept
   cell, which lies in `K.faces`, is off every lake (`kept_not_mem_lake`).
2. **Far faces of lake boundary darts lie in `K.faces`.**  Let `d` be a boundary dart of the lake:
   `faceOf d ∈ lakeOf K k` and `faceOf (α d) ∉ lakeOf K k`.  Then `faceOf d ∉ K.faces` by 1.  If
   also `faceOf (α d) ∉ K.faces`, the edge of `d` is not a boundary edge of `K.faces` (neither `d`
   nor `α d` has its face in `K.faces`), so the reach of `Π_k` crosses it
   (`ExteriorComponent.Reach.alpha`) and `faceOf (α d) ∈ lakeOf K k`, a contradiction.  Hence
   `faceOf (α d) ∈ K.faces` and `faceOf (α (α d)) = faceOf d ∉ K.faces`: `α d` is a boundary dart
   of `K.faces`, i.e. `α d ∈ K.boundary.cycle` (`lake_boundary_subset_cycle`).
3. **Correction of the lane text (loud).**  The lane asks that every dart of
   `invDarts X K.firstArc.darts` be a boundary dart of `lakeOf K i`.  With the repo convention
   `IsBoundaryDart M F d := faceOf d ∈ F ∧ faceOf (α d) ∉ F`, this is FALSE: such a dart `d`
   is a boundary dart of `K.faces`, so `faceOf d ∈ K.faces`, which is off the lake.  The true
   statement is for the reversed darts: for `d ∈ invDarts X K.firstArc.darts`, `α d` is a
   boundary dart of `lakeOf K i`; equivalently every dart of `K.firstArc.darts` is
   (`LakeArc.lean`: `firstArc_isBoundaryDart_lake`, `invArc_subset_lake_boundary`).
4. **Count.**  Among the indices `m : Fin X.rCellCount`, those with `Π_m ∈ lakeOf K k` miss the
   kept index, so they number fewer than `X.rCellCount` (`Finset.card_lt_card`, witness
   `K.kept`).  Removing also `k` (which differs from `K.kept`, since `Π_k ∉ K.faces`) leaves at
   most `X.rCellCount - 2` indices (`LakeCount.lean`).

No interface of another lane is assumed: lanes 05 and 09 supply only the same `ExteriorComponent`
API, which is on disk.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded HullSC WordMetric Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The lake holding a cell**: the piece of the face of `cell X k` in the complement of the
cell pocket face set, reached by moving around faces and crossing edges off its boundary. -/
noncomputable def lakeOf (K : CellPocketFaceSet D eps X i j) (k : Fin X.rCellCount) :
    Finset X.toCombMap.Face :=
  ExteriorComponent.component X.toCombMap K.faces (cell X k).face

theorem lakeOf_eq (K : CellPocketFaceSet D eps X i j) (k : Fin X.rCellCount) :
    lakeOf K k = ExteriorComponent.component X.toCombMap K.faces (cell X k).face :=
  rfl

/-- A cell lies in its own lake. -/
theorem cell_mem_lakeOf (K : CellPocketFaceSet D eps X i j) (k : Fin X.rCellCount) :
    (cell X k).face ∈ lakeOf K k := by
  rw [lakeOf_eq]
  exact ExteriorComponent.self_mem_component _

/-- **The lake of a cell off the face set is off the face set.** -/
theorem not_mem_faces_of_mem_lakeOf (K : CellPocketFaceSet D eps X i j) {k : Fin X.rCellCount}
    (hk : (cell X k).face ∉ K.faces) {f : X.toCombMap.Face} (hf : f ∈ lakeOf K k) :
    f ∉ K.faces := by
  rw [lakeOf_eq] at hf
  exact ExteriorComponent.not_mem_of_mem_component hk hf

/-- **The kept cell is off the lake** of every cell off the face set. -/
theorem kept_not_mem_lake (K : CellPocketFaceSet D eps X i j) {k : Fin X.rCellCount}
    (hk : (cell X k).face ∉ K.faces) : (cell X K.kept).face ∉ lakeOf K k :=
  fun hmem => not_mem_faces_of_mem_lakeOf K hk hmem K.kept_mem

/-- The kept index differs from every cell off the face set. -/
theorem kept_ne_of_not_mem (K : CellPocketFaceSet D eps X i j) {k : Fin X.rCellCount}
    (hk : (cell X k).face ∉ K.faces) : K.kept ≠ k := by
  intro h
  apply hk
  rw [← h]
  exact K.kept_mem

/-- **The far face of a lake boundary dart lies in the face set.** -/
theorem faceOf_alpha_mem_faces_of_isBoundaryDart_lake (K : CellPocketFaceSet D eps X i j)
    {k : Fin X.rCellCount} (hk : (cell X k).face ∉ K.faces) {d : X.toCombMap.Dart}
    (hd : Surgery.MapCollapse.IsBoundaryDart X.toCombMap (lakeOf K k) d) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ K.faces := by
  have hdin : X.toCombMap.faceOf d ∈ lakeOf K k := And.left hd
  have hdout : X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ lakeOf K k := And.right hd
  have hdoff : X.toCombMap.faceOf d ∉ K.faces := not_mem_faces_of_mem_lakeOf K hk hdin
  by_contra hout
  apply hdout
  have hoff : ¬ ExteriorComponent.BoundaryEdge X.toCombMap K.faces d := by
    intro hb
    rcases hb with hb | hb
    · exact hdoff (And.left hb)
    · exact hout (And.left hb)
  rw [lakeOf_eq] at hdin ⊢
  obtain ⟨y, hy, hreach⟩ := ExteriorComponent.mem_component_iff.mp hdin
  exact ExteriorComponent.mem_component_iff.mpr
    ⟨X.toCombMap.alpha d, rfl, (hreach.of_faceOf_eq hy).alpha hoff⟩

/-- **Lake boundary darts reverse into the boundary cycle** (`lake_boundary_subset_cycle`): the
reversal of every boundary dart of the lake of a cell off the face set is a boundary dart of the
face set, so it lies on `K.boundary.cycle = s₁ t̄₁ s₂ t̄₂`. -/
theorem lake_boundary_subset_cycle (K : CellPocketFaceSet D eps X i j) {k : Fin X.rCellCount}
    (hk : (cell X k).face ∉ K.faces) (d : X.toCombMap.Dart)
    (hd : Surgery.MapCollapse.IsBoundaryDart X.toCombMap (lakeOf K k) d) :
    X.toCombMap.alpha d ∈ K.boundary.cycle := by
  have h₁ : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ K.faces :=
    faceOf_alpha_mem_faces_of_isBoundaryDart_lake K hk hd
  have h₂ : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉ K.faces := by
    rw [X.toCombMap.alpha_involutive d]
    exact not_mem_faces_of_mem_lakeOf K hk (And.left hd)
  exact (K.boundary.cycle_mem_iff (X.toCombMap.alpha d)).mpr (And.intro h₁ h₂)

/-- The reversal of a lake boundary dart lies on one of the four pieces `s₁`, `t̄₁`, `s₂`, `t̄₂`
of the boundary cycle. -/
theorem lake_boundary_mem_pieces (K : CellPocketFaceSet D eps X i j) {k : Fin X.rCellCount}
    (hk : (cell X k).face ∉ K.faces) (d : X.toCombMap.Dart)
    (hd : Surgery.MapCollapse.IsBoundaryDart X.toCombMap (lakeOf K k) d) :
    X.toCombMap.alpha d ∈ K.firstSide ∨ X.toCombMap.alpha d ∈ invDarts X K.firstArc.darts ∨
      X.toCombMap.alpha d ∈ K.secondSide ∨
        X.toCombMap.alpha d ∈ invDarts X K.secondArc.darts := by
  have hmem := lake_boundary_subset_cycle K hk d hd
  rw [K.decomposition] at hmem
  simpa only [List.mem_append, or_assoc] using hmem

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lakeOf
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lakeOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.cell_mem_lakeOf
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.not_mem_faces_of_mem_lakeOf
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.kept_not_mem_lake
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.kept_ne_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.faceOf_alpha_mem_faces_of_isBoundaryDart_lake
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lake_boundary_subset_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lake_boundary_mem_pieces
