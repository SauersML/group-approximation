import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickRegionLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# The region statement with cells on the walk, from three unlinked darts

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-35.

**LOUD: `ExtremalJordanPickPoolRegionStatement` (lane gl-p10-34) is NOT proved here, and it may be
FALSE.**  G-faces (inner faces of value `1` that are not relator cells) can leave the only
arc-free inside class holding every relator cell (see `Piece10Live/ExtremalJordanPickRegion`).
This file proves the **corrected** statement `ExtremalJordanPickRegionCellsStatement` instead.
It adds one hypothesis: the face of every walk dart is a relator cell.

The corrected statement is reduced to ONE open Statement, `ExtremalJordanPickRegionThreeStatement`
(under not-A, three walk darts are pairwise unlinked), by
`extremalJordanPickRegion_region_of_three`.  LOUD: the Three statement is logically STRONGER than
the Cells statement and strictly smaller in proof content.  Case A, the arc pigeonhole and the
kept-cell bookkeeping are proved here.  It held on every model instance at 3 to 6 darts.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **OPEN (lane gl-p10-35).**  Under the premises of `ExtremalJordanPickPoolRegionStatement`
and not-A, three walk darts are pairwise not linked.  LOUD: logically STRONGER than
`ExtremalJordanPickRegionCellsStatement`, strictly smaller in proof content; true in the model at
3 to 6 darts (see `Piece10Live/ExtremalJordanPickRegion`). -/
def ExtremalJordanPickRegionThreeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ExtremalJordanPickRegionOutsideCovered K →
        ∃ r₁ ∈ K.boundary.cycle, ∃ r₂ ∈ K.boundary.cycle, ∃ r₃ ∈ K.boundary.cycle,
          ¬ExtremalJordanPickRegionLinked K r₁ r₂ ∧ ¬ExtremalJordanPickRegionLinked K r₁ r₃ ∧
            ¬ExtremalJordanPickRegionLinked K r₂ r₃

/-- **The corrected region statement.**  This is `ExtremalJordanPickPoolRegionStatement` with one
more hypothesis: the face of every walk dart is a relator cell.  It is logically weaker than
`ExtremalJordanPickPoolRegionStatement`. -/
def ExtremalJordanPickRegionCellsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      (∀ d ∈ K.boundary.cycle, ∃ i : Fin X.rCellCount, (cell X i).face = X.toCombMap.faceOf d) →
        ∃ r : X.toCombMap.Dart, ExtremalJordanPickPoolRegion K r

section PickRegionReduction

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Linking is symmetric.** -/
theorem extremalJordanPickRegion_linked_symm (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} (h : ExtremalJordanPickRegionLinked K x y) :
    ExtremalJordanPickRegionLinked K y x := by
  unfold ExtremalJordanPickRegionLinked at h ⊢
  exact Relation.EqvGen.symm _ _ h

/-- **Case A when not-A fails**: a class outside `K.faces` that meets neither the exterior face
nor the source face is a region class. -/
theorem extremalJordanPickRegion_of_not_covered (K : PocketFaceSet D eps X lo hi)
    (h : ¬ExtremalJordanPickRegionOutsideCovered K) :
    ∃ r : X.toCombMap.Dart, ExtremalJordanPickPoolRegion K r := by
  unfold ExtremalJordanPickRegionOutsideCovered at h
  obtain ⟨r, hr⟩ := Classical.not_forall.mp h
  obtain ⟨hrK, hno⟩ := Classical.not_imp.mp hr
  refine ⟨r, ?_⟩
  unfold ExtremalJordanPickPoolRegion
  exact Or.inl ⟨hrK, fun x hx hrx => hno (Or.inl ⟨x, hx, hrx⟩),
    fun x hx hrx => hno (Or.inr ⟨x, hx, hrx⟩)⟩

/-- **Arc pigeonhole**: among three pairwise unlinked darts, one meets neither arc.  Two darts
meeting the same arc are linked (`extremalJordanPickRegion_linked_of_meets`). -/
theorem extremalJordanPickRegion_free_of_three (K : PocketFaceSet D eps X lo hi)
    {r₁ r₂ r₃ : X.toCombMap.Dart} (h₁₂ : ¬ExtremalJordanPickRegionLinked K r₁ r₂)
    (h₁₃ : ¬ExtremalJordanPickRegionLinked K r₁ r₃)
    (h₂₃ : ¬ExtremalJordanPickRegionLinked K r₂ r₃) :
    ∃ r o : X.toCombMap.Dart, (r = r₁ ∨ r = r₂ ∨ r = r₃) ∧ (o = r₁ ∨ o = r₂ ∨ o = r₃) ∧
      ¬ExtremalJordanPickRegionLinked K r o ∧
      ¬ExtremalJordanPickRegionMeets K r K.targetArc.darts ∧
      ¬ExtremalJordanPickRegionMeets K r (invDarts X K.sourceArc.darts) := by
  have hT : ∀ a b : X.toCombMap.Dart, ExtremalJordanPickRegionMeets K a K.targetArc.darts →
      ExtremalJordanPickRegionMeets K b K.targetArc.darts → ExtremalJordanPickRegionLinked K a b :=
    fun a b ha hb => extremalJordanPickRegion_linked_of_meets K (Or.inl rfl) ha hb
  have hS : ∀ a b : X.toCombMap.Dart,
      ExtremalJordanPickRegionMeets K a (invDarts X K.sourceArc.darts) →
      ExtremalJordanPickRegionMeets K b (invDarts X K.sourceArc.darts) →
      ExtremalJordanPickRegionLinked K a b :=
    fun a b ha hb => extremalJordanPickRegion_linked_of_meets K (Or.inr rfl) ha hb
  have m : ∀ a : X.toCombMap.Dart,
      ¬(¬ExtremalJordanPickRegionMeets K a K.targetArc.darts ∧
        ¬ExtremalJordanPickRegionMeets K a (invDarts X K.sourceArc.darts)) →
      ExtremalJordanPickRegionMeets K a K.targetArc.darts ∨
        ExtremalJordanPickRegionMeets K a (invDarts X K.sourceArc.darts) := by
    intro a ha
    by_contra hn
    exact ha ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
  by_cases c₁ : ¬ExtremalJordanPickRegionMeets K r₁ K.targetArc.darts ∧
      ¬ExtremalJordanPickRegionMeets K r₁ (invDarts X K.sourceArc.darts)
  · exact ⟨r₁, r₂, Or.inl rfl, Or.inr (Or.inl rfl), h₁₂, c₁.1, c₁.2⟩
  by_cases c₂ : ¬ExtremalJordanPickRegionMeets K r₂ K.targetArc.darts ∧
      ¬ExtremalJordanPickRegionMeets K r₂ (invDarts X K.sourceArc.darts)
  · exact ⟨r₂, r₁, Or.inr (Or.inl rfl), Or.inl rfl,
      fun h => h₁₂ (extremalJordanPickRegion_linked_symm K h), c₂.1, c₂.2⟩
  by_cases c₃ : ¬ExtremalJordanPickRegionMeets K r₃ K.targetArc.darts ∧
      ¬ExtremalJordanPickRegionMeets K r₃ (invDarts X K.sourceArc.darts)
  · exact ⟨r₃, r₁, Or.inr (Or.inr rfl), Or.inl rfl,
      fun h => h₁₃ (extremalJordanPickRegion_linked_symm K h), c₃.1, c₃.2⟩
  exfalso
  rcases m r₁ c₁ with a₁ | a₁ <;> rcases m r₂ c₂ with a₂ | a₂ <;>
    rcases m r₃ c₃ with a₃ | a₃ <;>
    first
    | exact h₁₂ (hT _ _ a₁ a₂)
    | exact h₁₂ (hS _ _ a₁ a₂)
    | exact h₁₃ (hT _ _ a₁ a₃)
    | exact h₁₃ (hS _ _ a₁ a₃)
    | exact h₂₃ (hT _ _ a₂ a₃)
    | exact h₂₃ (hS _ _ a₂ a₃)

/-- **Case B from a free dart**: a walk dart `r` meeting neither arc, unlinked from a walk dart
`o` whose face is a relator cell, is a region class. -/
theorem extremalJordanPickRegion_region_of_free (K : PocketFaceSet D eps X lo hi)
    {r o : X.toCombMap.Dart} (hr : r ∈ K.boundary.cycle) (ho : o ∈ K.boundary.cycle)
    (hro : ¬ExtremalJordanPickRegionLinked K r o)
    (hT : ¬ExtremalJordanPickRegionMeets K r K.targetArc.darts)
    (hS : ¬ExtremalJordanPickRegionMeets K r (invDarts X K.sourceArc.darts))
    (i : Fin X.rCellCount) (hi : (cell X i).face = X.toCombMap.faceOf o) :
    ExtremalJordanPickPoolRegion K r := by
  unfold ExtremalJordanPickPoolRegion
  refine Or.inr ⟨extremalJordanPickPool_face_mem_of_cycle K hr, ⟨i, ?_, ?_⟩, ?_⟩
  · rw [hi]
    exact extremalJordanPickPool_face_mem_of_cycle K ho
  · intro x hx hrx
    exact hro (extremalJordanPickRegion_linked_of_class K
      (Relation.EqvGen.trans _ _ _ hrx (extremalJordanPickRegion_eqvGen_of_face K (hx.trans hi))))
  · intro d hd hrd
    rcases List.mem_append.mp hd with hd | hd
    · exact hT ⟨d, hd, hrd⟩
    · exact hS ⟨d, hd, hrd⟩

/-- **A region class for one pocket**, from three unlinked walk darts under not-A and relator
cells on the walk. -/
theorem extremalJordanPickRegion_exists (K : PocketFaceSet D eps X lo hi)
    (hthree : ExtremalJordanPickRegionOutsideCovered K →
      ∃ r₁ ∈ K.boundary.cycle, ∃ r₂ ∈ K.boundary.cycle, ∃ r₃ ∈ K.boundary.cycle,
        ¬ExtremalJordanPickRegionLinked K r₁ r₂ ∧ ¬ExtremalJordanPickRegionLinked K r₁ r₃ ∧
          ¬ExtremalJordanPickRegionLinked K r₂ r₃)
    (hcell : ∀ d ∈ K.boundary.cycle,
      ∃ i : Fin X.rCellCount, (cell X i).face = X.toCombMap.faceOf d) :
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
    obtain ⟨i, hi⟩ := hcell o (hmem o ho)
    exact ⟨r, extremalJordanPickRegion_region_of_free K (hmem r hr) (hmem o ho) hro hT hS i hi⟩
  · exact extremalJordanPickRegion_of_not_covered K hA

end PickRegionReduction

/-- **The endpoint**: the Three statement gives the corrected region statement. -/
theorem extremalJordanPickRegion_region_of_three
    (h : ExtremalJordanPickRegionThreeStatement.{u, w, v}) :
    ExtremalJordanPickRegionCellsStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose hcell
  exact extremalJordanPickRegion_exists K
    (h D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose) hcell

/-- **The corrected statement is weaker than the lane-34 target.** -/
theorem extremalJordanPickRegion_cells_of_poolRegion
    (h : ExtremalJordanPickPoolRegionStatement.{u, w, v}) :
    ExtremalJordanPickRegionCellsStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose _
  exact h D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickRegionThreeStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickRegionCellsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_linked_symm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_of_not_covered
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_free_of_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_region_of_free
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_exists
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_region_of_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_cells_of_poolRegion
