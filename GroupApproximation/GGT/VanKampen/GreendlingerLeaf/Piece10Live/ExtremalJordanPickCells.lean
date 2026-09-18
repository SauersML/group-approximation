import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickRegionReduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickStep
import GroupApproximation.Meta.AxiomGuard

/-!
# A pool class from three unlinked darts, when every walk class holds a relator cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-37.

**LOUD: the lane's Option 1 is IMPOSSIBLE.**  It asked for a proof that the face of every walk
dart is a relator cell.  `PocketFaceSet.faces` is an arbitrary face set, and no premise of
`ExtremalJordanPickRunStatement` excludes G-faces (inner faces of boundary value `1`, legal in a
`DiscDiagram`, not counted by `LeastArea`) on the walk.  A loop labelled `comp λ 1` is a legal
letter, so G-face balloons can sit on the walk.

This file weakens the lane-35 hypothesis.  `ExtremalJordanPickCellsClass K` asks only that the
face class of every walk dart contain the face of a relator cell of `K.faces`.  The lane-35
hypothesis implies it (`extremalJordanPickCells_class_of_cells`).  Under it, three pairwise
unlinked walk darts give a region class (`extremalJordanPickCells_region_exists`), hence a pool
class (`extremalJordanPickCells_pool_exists`).  The free dart `r` of the arc pigeonhole is
unlinked from a walk dart `o`, and the relator cell in the class of `o` is avoided by the class
of `r`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section PickCells

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Every walk class holds a relator cell**: the face class of every walk dart contains the
face of a relator cell of `K.faces`.  A G-face may lie on the walk, as long as its class also
contains a relator cell. -/
def ExtremalJordanPickCellsClass (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ d ∈ K.boundary.cycle, ∃ i : Fin X.rCellCount, (cell X i).face ∈ K.faces ∧
    ∃ x : X.toCombMap.Dart, X.toCombMap.faceOf x = (cell X i).face ∧
      Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) d x

/-- **Relator cells on the walk give relator cells in every walk class**: the lane-35 hypothesis
of `ExtremalJordanPickRegionCellsStatement` implies `ExtremalJordanPickCellsClass`. -/
theorem extremalJordanPickCells_class_of_cells (K : PocketFaceSet D eps X lo hi)
    (h : ∀ d ∈ K.boundary.cycle,
      ∃ i : Fin X.rCellCount, (cell X i).face = X.toCombMap.faceOf d) :
    ExtremalJordanPickCellsClass K := by
  intro d hd
  obtain ⟨i, hi⟩ := h d hd
  refine ⟨i, ?_, d, hi.symm, Relation.EqvGen.refl _⟩
  rw [hi]
  exact extremalJordanPickPool_face_mem_of_cycle K hd

/-- **Case B from a free dart**: a walk dart `r` meeting neither arc, unlinked from a dart `o`
whose class holds a relator cell of `K.faces`, is a region class. -/
theorem extremalJordanPickCells_region_of_free (K : PocketFaceSet D eps X lo hi)
    {r o : X.toCombMap.Dart} (hr : r ∈ K.boundary.cycle)
    (hro : ¬ExtremalJordanPickRegionLinked K r o)
    (hT : ¬ExtremalJordanPickRegionMeets K r K.targetArc.darts)
    (hS : ¬ExtremalJordanPickRegionMeets K r (invDarts X K.sourceArc.darts))
    (i : Fin X.rCellCount) (hiK : (cell X i).face ∈ K.faces) (x : X.toCombMap.Dart)
    (hx : X.toCombMap.faceOf x = (cell X i).face)
    (hox : Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) o x) :
    ExtremalJordanPickPoolRegion K r := by
  unfold ExtremalJordanPickPoolRegion
  refine Or.inr ⟨extremalJordanPickPool_face_mem_of_cycle K hr, ⟨i, hiK, ?_⟩, ?_⟩
  · intro y hy hry
    exact hro (extremalJordanPickRegion_linked_of_class K
      (Relation.EqvGen.trans _ _ _ hry (Relation.EqvGen.trans _ _ _
        (extremalJordanPickRegion_eqvGen_of_face K (hy.trans hx.symm))
        (Relation.EqvGen.symm _ _ hox))))
  · intro d hd hrd
    rcases List.mem_append.mp hd with hd | hd
    · exact hT ⟨d, hd, hrd⟩
    · exact hS ⟨d, hd, hrd⟩

/-- **A region class for one pocket**, from three unlinked walk darts under not-A and a relator
cell in every walk class. -/
theorem extremalJordanPickCells_region_exists (K : PocketFaceSet D eps X lo hi)
    (hthree : ExtremalJordanPickRegionOutsideCovered K →
      ∃ r₁ ∈ K.boundary.cycle, ∃ r₂ ∈ K.boundary.cycle, ∃ r₃ ∈ K.boundary.cycle,
        ¬ExtremalJordanPickRegionLinked K r₁ r₂ ∧ ¬ExtremalJordanPickRegionLinked K r₁ r₃ ∧
          ¬ExtremalJordanPickRegionLinked K r₂ r₃)
    (hcls : ExtremalJordanPickCellsClass K) :
    ∃ r : X.toCombMap.Dart, ExtremalJordanPickPoolRegion K r := by
  by_cases hA : ExtremalJordanPickRegionOutsideCovered K
  · obtain ⟨r₁, hr₁, r₂, hr₂, r₃, hr₃, h₁₂, h₁₃, h₂₃⟩ := hthree hA
    obtain ⟨r, o, hr, ho, hro, hT, hS⟩ := extremalJordanPickRegion_free_of_three K h₁₂ h₁₃ h₂₃
    have hmem : ∀ z : X.toCombMap.Dart, (z = r₁ ∨ z = r₂ ∨ z = r₃) → z ∈ K.boundary.cycle := by
      intro z hz
      rcases hz with h | h | h
      · rw [h]
        exact hr₁
      · rw [h]
        exact hr₂
      · rw [h]
        exact hr₃
    obtain ⟨i, hiK, x, hx, hox⟩ := hcls o (hmem o ho)
    exact ⟨r, extremalJordanPickCells_region_of_free K (hmem r hr) hro hT hS i hiK x hx hox⟩
  · exact extremalJordanPickRegion_of_not_covered K hA

/-- **A pool class for one pocket**, from three unlinked walk darts under not-A and a relator
cell in every walk class. -/
theorem extremalJordanPickCells_pool_exists (K : PocketFaceSet D eps X lo hi)
    (hthree : ExtremalJordanPickRegionOutsideCovered K →
      ∃ r₁ ∈ K.boundary.cycle, ∃ r₂ ∈ K.boundary.cycle, ∃ r₃ ∈ K.boundary.cycle,
        ¬ExtremalJordanPickRegionLinked K r₁ r₂ ∧ ¬ExtremalJordanPickRegionLinked K r₁ r₃ ∧
          ¬ExtremalJordanPickRegionLinked K r₂ r₃)
    (hcls : ExtremalJordanPickCellsClass K) :
    ∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r := by
  obtain ⟨r, hr⟩ := extremalJordanPickCells_region_exists K hthree hcls
  exact ⟨r, extremalJordanPickPool_of_region K hr⟩

end PickCells

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCellsClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_class_of_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_region_of_free
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_region_exists
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_pool_exists
