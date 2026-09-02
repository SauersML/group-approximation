import GroupApproximation.GGT.KazhdanHypGirthEightBuild

/-!
# Cactus producer adapters

The landed cactus realization theorem starts with an oriented algebraic
`Lemma44OrientedRelatorDiagram`; it does not manufacture that diagram from a
word.  Likewise, `CactusRelatorRetyping` is a certificate and not an
availability theorem.  This file records the exact smaller inputs which the
landed constructors consume, and proves both adapter implications by name.

The orientation adapter uses
`Lemma44RelatorDiagramBoundary.exists_reduced` followed by
`Lemma44ReducedRelatorDiagram.exists_oriented`.  The retyping adapter uses
`CactusFoldChain.toRetyping`.  Thus a future producer can discharge the two
named source predicates without changing the Build consumer.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightBuild

open GroupApproximation.HullSC
open GroupApproximation.KazhdanHyp
open GroupApproximation.Manuscript.NonMF.TorsionFree

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## The algebraic source for an oriented cactus boundary -/

/-- A least-area boundary source together with the small-cancellation datum
needed to orient its reduced factor list. -/
def OrientedCactusBoundarySource : Prop :=
  ∀ (w : List (TriangularHodgeLayer.SignedGenerator Generator)),
    PresentedWordIsTrivial (T := T) w →
    (w.map freeLetter).prod ≠ 1 →
    ∃ (A : Alphabet (FreeGroup Generator)) (R : ℕ)
      (D : Lemma44RelatorDiagramBoundary A
        (triangleRelatorWords T) R),
      D.boundaryWord = w.map freeLetter ∧
      ∃ (E : GGT.RelGenSet (FreeGroup Generator) PEmpty)
        (eps : ℕ) (mu : ℝ) (rho : ℕ),
        RelWord.IsSmallCancellation E (triangleRelatorWords T) eps mu rho

theorem orientedCactusBoundaryProducer_of_source
    (hsource : OrientedCactusBoundarySource (T := T)) :
    OrientedCactusBoundaryProducer (T := T) := by
  intro w hw hfree
  obtain ⟨A, R, D, hboundary, E, eps, mu, rho, hsc⟩ :=
    hsource w hw hfree
  obtain ⟨Dred⟩ := D.exists_reduced
  obtain ⟨Z⟩ := Dred.exists_oriented hsc
  exact ⟨A, R, Z, hboundary⟩

theorem cactusBoundaryInput_of_source
    (hsource : OrientedCactusBoundarySource (T := T)) :
    CactusBoundaryInput (T := T) :=
  cactusBoundaryInput_of_orientedCactusBoundaryProducer
    (orientedCactusBoundaryProducer_of_source hsource)

/-- The source predicate already supplies exactly the boundary spelling needed
by the Build-level producer.  Its model is vacuous for the empty free group. -/
theorem orientedCactusBoundaryProducer_empty_model :
    OrientedCactusBoundaryProducer (T := emptyTriangleTableBuild) :=
  orientedCactusBoundaryProducer_trivialGroup_model

/-! ## The topological source for cactus retyping -/

/-- A landed fold-chain source: every reduced diagram admits a finite chain of
concrete cactus base-cell deletions ending in relator-cell coverage. -/
def CactusFoldChainAvailability : Prop :=
  ∀ (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)),
    Delta.Reduced →
      ∃ k, Nonempty (VanKampen.CactusFoldChain Delta k)

theorem cactusRelatorRetypingAvailability_of_foldChainAvailability
    (hfold : CactusFoldChainAvailability (T := T)) :
    CactusRelatorRetypingAvailability (T := T) := by
  intro Delta hred
  obtain ⟨k, chain⟩ := hfold Delta hred
  exact ⟨chain.toRetyping Delta.planar hred⟩

theorem baseCellElimination_of_foldChainAvailability
    (hfold : CactusFoldChainAvailability (T := T)) :
    BaseCellElimination (T := T) :=
  baseCellElimination_of_cactusRelatorRetypingAvailability
    (cactusRelatorRetypingAvailability_of_foldChainAvailability hfold)

/-! ## The one-step covered-diagram source -/

/-- A relator-cell cover is the terminal object of the landed fold chain.  The
constructor below is useful when a future planar deletion proof gives the
cover directly rather than an explicit list of intermediate folds. -/
def RelatorCellCoverAvailability : Prop :=
  ∀ (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)),
    Delta.Reduced → Nonempty (VanKampen.RelatorCellCover Delta)

theorem cactusFoldChainAvailability_of_relatorCellCoverAvailability
    (hcover : RelatorCellCoverAvailability (T := T)) :
    CactusFoldChainAvailability (T := T) := by
  intro Delta hred
  obtain ⟨cover⟩ := hcover Delta hred
  exact ⟨0, ⟨VanKampen.CactusFoldChain.done cover⟩⟩

theorem cactusRelatorRetypingAvailability_of_relatorCellCoverAvailability
    (hcover : RelatorCellCoverAvailability (T := T)) :
    CactusRelatorRetypingAvailability (T := T) :=
  cactusRelatorRetypingAvailability_of_foldChainAvailability
    (cactusFoldChainAvailability_of_relatorCellCoverAvailability hcover)

theorem baseCellElimination_of_relatorCellCoverAvailability
    (hcover : RelatorCellCoverAvailability (T := T)) :
    BaseCellElimination (T := T) :=
  baseCellElimination_of_foldChainAvailability
    (cactusFoldChainAvailability_of_relatorCellCoverAvailability hcover)

/-! ## Direct model checks for the landed fold endpoint -/

/-- The terminal `done` constructor is inhabited whenever coverage is given;
this checks the exact zero-fold endpoint used by the adapter. -/
theorem cactusFoldChain_done_model
    {Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)}
    (cover : VanKampen.RelatorCellCover Delta) :
    Nonempty (VanKampen.CactusFoldChain Delta 0) := by
  exact ⟨VanKampen.CactusFoldChain.done cover⟩

theorem cactusRetyping_of_covered_model
    {Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)}
    (cover : VanKampen.RelatorCellCover Delta) (hred : Delta.Reduced) :
    Nonempty (VanKampen.CactusRelatorRetyping Delta) := by
  exact ⟨(VanKampen.CactusFoldChain.done cover).toRetyping
    Delta.planar hred⟩

/-! ## The composed source-level consumer -/

/-! ## The composed consumer -/

/-- The exact Build consumer after replacing the two opaque named producers by
their landed algebraic and topological source certificates. -/
theorem presented_isHyperbolicGroup_of_source_certificates
    {d delta : ℕ} (hchecks : GirthEightChecks T d)
    (hword : FarPointBoundaryWord (T := T))
    (hsource : OrientedCactusBoundarySource (T := T))
    (hfold : CactusFoldChainAvailability (T := T))
    (hstar : StarLayerConstructionCertificateInput (T := T)) :
    Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T) := by
  exact presented_isHyperbolicGroup_of_cactus_star_build_of_all_certificates
    (delta := delta) hchecks hword
    (orientedCactusBoundaryProducer_of_source hsource)
    (cactusRelatorRetypingAvailability_of_foldChainAvailability hfold)
    hstar

theorem presented_isHyperbolicGroup_of_source_cover_and_star
    {d delta : ℕ} (hchecks : GirthEightChecks T d)
    (hword : FarPointBoundaryWord (T := T))
    (hsource : OrientedCactusBoundarySource (T := T))
    (hcover : RelatorCellCoverAvailability (T := T))
    (hstar : StarLayerConstructionCertificateInput (T := T)) :
    Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T) := by
  exact presented_isHyperbolicGroup_of_cactus_star_build
    (delta := delta) hchecks hword (cactusBoundaryInput_of_source hsource)
    (baseCellElimination_of_relatorCellCoverAvailability hcover)
    (starLayerConstruction_of_certificate hstar)

theorem orientedCactusBoundaryProducer_empty_table_model :
    OrientedCactusBoundaryProducer (T := emptyTriangleTableBuild) :=
  orientedCactusBoundaryProducer_trivialGroup_model

theorem cactusBoundaryInput_empty_table_model :
    CactusBoundaryInput (T := emptyTriangleTableBuild) :=
  cactusBoundaryInput_trivialGroup_model

end Table
end KazhdanHypGirthEightBuild
end GGT
end GroupApproximation
