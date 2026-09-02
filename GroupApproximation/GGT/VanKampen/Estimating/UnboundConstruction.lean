import GroupApproximation.GGT.VanKampen.Estimating.Assembly

/-!
# The Lemma 62 unbound-budget constructor

This file isolates the geometric part of Osin's Appendix Lemma 62 from the
already proved averaging calculation.  A complementary-component partition
certificate gives the strict square-root bound on the selected unbound arcs;
the final numerical threshold is supplied separately at the parameter value
chosen by the estimating construction.  The source is Osin, Appendix Lemma
62, with the partition certificate corresponding to its complementary-disc
decomposition and averaging inequality.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open UnboundEstimate

universe u w v

/-! ## The strictly smaller Lemma 62 geometric estimate -/

/-- The square-root part of the Lemma 62 output, with the numerical threshold
removed.  It is the single budget estimate which remains after the finite
selection and deletion data have fixed the scaffold. -/
def UnboundLengthBudgetStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta),
    IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      (scaffold.partition.unboundTotal : ℝ) <
        (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ)

/-- A complementary-component averaging certificate is exactly sufficient for
the budget field of `Lemma62Data`.  The equality in the certificate fixes the
total to the canonical partition total of the selected scaffold. -/
theorem lemma62Data_of_partitionCertificate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    {d : ℕ}
    (certificate : PartitionUnboundCertificate Delta.rCellCount d
      (Real.sqrt (rho : ℝ)) (scaffold.partition.unboundTotal : ℝ))
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  refine ⟨{ unbound_lt := ?_, threshold := hthreshold }⟩
  exact certificate.total_lt

/-! ## The certificate-to-budget bridge -/

/-- This is the face-partition producer interface for Lemma 62.  It asks only
for the complementary-component certificate at each fixed diagram and keeps
the finite scaffold and boundary hypotheses supplied by the selection layer. -/
def PartitionUnboundCertificateStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta),
    IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      ∃ d : ℕ,
        PartitionUnboundCertificate Delta.rCellCount d
          (Real.sqrt (rho : ℝ))
          (scaffold.partition.unboundTotal : ℝ)

/-- The partition producer proves the strictly smaller square-root budget.
This is the numerical conclusion of Appendix Lemma 62 after the geometric
complementary-disc construction has been supplied. -/
theorem unboundLengthBudget_of_partitionCertificates
    (hcertificate : PartitionUnboundCertificateStatement.{u, w, v}) :
    UnboundLengthBudgetStatement.{u, w, v} := by
  intro G _ Lambda D eps rho mu lambda c W hcondition Delta scaffold hboundary
  obtain ⟨d, certificate⟩ := hcertificate D eps rho mu lambda c
    hcondition Delta scaffold hboundary
  exact certificate.total_lt

/-- At parameters for which the square-root budget and the numerical
threshold are available, the full `Lemma62Data` object is constructed without
any further diagram argument. -/
theorem estimatingUnboundConstruction_at_of_lengthBudget
    (hbudget : UnboundLengthBudgetStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta)
    (hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord)
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  refine ⟨{ unbound_lt := ?_, threshold := hthreshold }⟩
  exact hbudget D eps rho mu lambda c hcondition Delta scaffold hboundary

/-! ## Degenerate models -/

/-- The empty-family model is vacuous in the positive-cell branch.  This
checks the budget interface against the same empty-family obstruction used by
the finite selection and deletion layers. -/
theorem unboundConstruction_emptyFamily_model
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (_hcondition : OsinCCondition D
      (∅ : Set (List (GGT.RelLetter G Lambda))) eps mu lambda c rho)
    (scaffold : EstimatingScaffold D eps Delta)
    (_hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord)
    (hcells : 0 < Delta.rCellCount) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  exact (no_positive_rCells_emptyFamily Delta hcells).elim

/-- In the one-cell model, vanishing unbound total gives the strict budget as
soon as `rho` is positive.  The remaining threshold is displayed explicitly,
so this model does not hide the large-`rho` numerical premise. -/
theorem lemma62Data_oneCell_zeroUnbound_model
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (hrcell : Delta.rCellCount = 1)
    (hunbound : scaffold.partition.unboundTotal = 0)
    (hrho : 0 < rho)
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  refine ⟨{ unbound_lt := ?_, threshold := hthreshold }⟩
  rw [hunbound, hrcell, Nat.cast_one, one_mul]
  exact Real.sqrt_pos.2 (by exact_mod_cast hrho)

/-- The averaging certificate has the exact empty-component model used by the
partition producer, and its numerical output is strict at the smallest
positive square-root parameter. -/
theorem partitionCertificate_empty_model_check :
    Nonempty (PartitionUnboundCertificate 1 0 1 0) :=
  partitionUnboundCertificate_emptyModel

end Estimating
end VanKampen
end GGT
end GroupApproximation
