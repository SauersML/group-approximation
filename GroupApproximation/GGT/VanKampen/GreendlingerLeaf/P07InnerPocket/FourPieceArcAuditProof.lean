import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInputProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21c: helpers for the reading part

These are the helpers for `pocketFourPieceInside_of_arcAuditResidual`
(`FourPieceArcAuditInside.lean`).  That theorem proves `PocketFourPieceInsideStatement`
(`FourPieceOffSplit.lean`) from the corrected residual `PocketFourPieceArcAuditResidualStatement`
(`FourPieceArcAuditStatement.lean`).
* **Branch 2**, or an all-`G₁` or all-`G₂` walk (clause 4b): the walk is one cell arc.  Read it as
  `[] ++ Ā ++ [] ++ ∅` (`ArcAudit.inside_of_arc_left`, `_right`).  The arc is nonempty because the
  walk is, so the inside clause is vacuous.
* **Otherwise** the proof of `pocketFourPieceInside_of_inputProofResidual` runs unchanged.
  - Labels use clause 2', whose exempt darts are already `G₁` or `G₂` labels.
  - Clause 4a applies because an entry outside `G₁` exists, and by
    `ArcAudit.exists_not_mem_right` it lies in the complement of the block.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **An entry off a block of a rotation lies in the complement.** -/
theorem ArcAudit.exists_not_mem_right {α : Type*} {P : α → Prop} {l U V : List α} {m : ℕ}
    (hm : l.rotate m = U ++ V) (hU : ∀ x ∈ U, P x) (hx : ∃ x ∈ l, ¬ P x) : ∃ x ∈ V, ¬ P x := by
  obtain ⟨x, hxl, hnx⟩ := hx
  have hmem : x ∈ U ++ V := by
    rw [← hm]
    exact List.mem_rotate.mpr hxl
  rcases List.mem_append.mp hmem with hxU | hxV
  · exact absurd (hU x hxU) hnx
  · exact ⟨x, hxV, hnx⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcAudit.exists_not_mem_right

/-- **A walk reading one arc is nonempty as an arc.** -/
theorem ArcAudit.length_ne_zero_of_rotate {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart} {n : ℕ}
    {cycle : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X faces outerWalk)
    (A : CyclicArc cycle) (hA : invDarts X (outerWalk.rotate n) = invDarts X A.darts) :
    A.length ≠ 0 := by
  intro h0
  have hd : A.darts = [] := List.eq_nil_of_length_eq_zero (by rw [A.darts_length]; exact h0)
  have hl := congrArg List.length hA
  rw [hd] at hl
  exact E.ne_nil (by simpa [invDarts] using hl)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcAudit.length_ne_zero_of_rotate

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
  {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
  {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
  {f : X.toCombMap.Face} {n : ℕ}

/-- **A walk reading one arc of `i` gives the reading part.** -/
theorem ArcAudit.inside_of_arc_left (E : EnclosedFaceSetSucc X faces outerWalk)
    (hf : f ∈ faces) (A : CyclicArc (cellDarts X i))
    (hA : invDarts X (outerWalk.rotate n) = invDarts X A.darts) :
    ∃ (n : ℕ) (R₁ R₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
      (A₂ : CyclicArc (cellDarts X j)),
      EnclosedFaceSetSucc X faces outerWalk ∧ f ∈ faces ∧
        invDarts X (outerWalk.rotate n) =
          R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts ∧
        ((((∀ r ∈ R₁, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
              (∀ r ∈ R₁, X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
            ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
              (∀ r ∈ R₂, X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
          ((∀ r ∈ R₁ ++ R₂,
              X.toCombMap.alpha r ∈ a.sideFrom j ∨ X.toCombMap.alpha r ∈ b.sideFrom i) ∧
            (A₁.length = 0 ∨ A₂.length = 0))) ∧
        (A₁.length = 0 → A₂.length = 0 → faces ⊆ sideFaces X.toCombMap K.walk) := by
  refine ⟨n, [], [], A, PocketRun.emptyArc _, E, hf, ?_,
    Or.inl ⟨Or.inl fun _ hx => by simp at hx, Or.inl fun _ hx => by simp at hx⟩,
    fun h0 _ => absurd h0 (ArcAudit.length_ne_zero_of_rotate E A hA)⟩
  rw [PocketRun.emptyArc_darts]
  simpa [invDarts] using hA

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcAudit.inside_of_arc_left

/-- **A walk reading one arc of `j` gives the reading part.** -/
theorem ArcAudit.inside_of_arc_right (E : EnclosedFaceSetSucc X faces outerWalk)
    (hf : f ∈ faces) (A : CyclicArc (cellDarts X j))
    (hA : invDarts X (outerWalk.rotate n) = invDarts X A.darts) :
    ∃ (n : ℕ) (R₁ R₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
      (A₂ : CyclicArc (cellDarts X j)),
      EnclosedFaceSetSucc X faces outerWalk ∧ f ∈ faces ∧
        invDarts X (outerWalk.rotate n) =
          R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts ∧
        ((((∀ r ∈ R₁, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
              (∀ r ∈ R₁, X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
            ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
              (∀ r ∈ R₂, X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
          ((∀ r ∈ R₁ ++ R₂,
              X.toCombMap.alpha r ∈ a.sideFrom j ∨ X.toCombMap.alpha r ∈ b.sideFrom i) ∧
            (A₁.length = 0 ∨ A₂.length = 0))) ∧
        (A₁.length = 0 → A₂.length = 0 → faces ⊆ sideFaces X.toCombMap K.walk) := by
  refine ⟨n, [], [], PocketRun.emptyArc _, A, E, hf, ?_,
    Or.inl ⟨Or.inl fun _ hx => by simp at hx, Or.inl fun _ hx => by simp at hx⟩,
    fun _ h0 => absurd h0 (ArcAudit.length_ne_zero_of_rotate E A hA)⟩
  rw [PocketRun.emptyArc_darts]
  simpa [invDarts] using hA

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcAudit.inside_of_arc_right

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
