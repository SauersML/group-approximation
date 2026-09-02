import GroupApproximation.GGT.VanKampen.Estimating.UnboundEmptyDisc

/-!
# The repaired Lemma 62 construction statement

`UnboundEmptyDisc` refutes `EstimatingUnboundConstructionStatement` twice
over.  This file states the form that matches Osin's Appendix Lemma 62
(arXiv `math/0411039`) and reduces it to a single geometric producer.

The source runs Lemma 62 on a reduced diagram with `n >= 1` R-cells, under
the hypothesis `(*)` that the estimating graph is simple with the two-gon
condition, and with `rho` chosen after `mu`; the closing line of Lemma 63
reads `rho > mu^{-2}`.  Three binders are added here for those three
readings: `0 < Delta.rCellCount`, `EstimatingGraphData`, and the numerical
threshold.  All three are already in scope at the one call site of the
statement, `estimatingDataConstruction_of_components`, except that the
threshold has to travel down from the parameter selection.

`exists_rho_threshold` proves the parameter choice is available: for every
positive `mu` there is a positive `rho` with `1 <= 2 * mu * sqrt rho`.

What is left after this file is `Lemma62ComponentPartitionStatement`: the
complementary components of the selected exterior arcs carry a Lemma 62
averaging certificate.  That is the contradiction argument of Osin's proof,
which cuts each component into a disc, applies Proposition 4.14 to the type
(A1) arcs, and contradicts either the maximality of the distinguished family
or the minimality of the cutting paths.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open UnboundEstimate

universe u w v

/-! ## The numerical threshold -/

/-- The threshold field forces a positive square root: at `sqrt rho = 0` it
reads `1 <= 0`. -/
theorem sqrt_pos_of_threshold {mu : ℝ} {rho : ℕ}
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    0 < Real.sqrt (rho : ℝ) := by
  rcases lt_or_eq_of_le (Real.sqrt_nonneg ((rho : ℝ))) with hpos | hzero
  · exact hpos
  · rw [← hzero, mul_zero] at hthreshold
    norm_num at hthreshold

/-- The threshold field forces `0 < rho`, so it strictly strengthens the
`_hrho` binder the statement carries now. -/
theorem rho_pos_of_threshold {mu : ℝ} {rho : ℕ}
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) : 0 < rho := by
  by_contra hrho
  have hzero : rho = 0 := by omega
  rw [hzero, Nat.cast_zero, Real.sqrt_zero, mul_zero] at hthreshold
  norm_num at hthreshold

/-- Osin's parameter choice `rho > mu^{-2}` is available: every positive `mu`
admits a positive `rho` meeting the threshold.  The witness is the ceiling of
`(2 * mu)^{-2}`. -/
theorem exists_rho_threshold {mu : ℝ} (hmu : 0 < mu) :
    ∃ rho : ℕ, 0 < rho ∧ 1 ≤ 2 * mu * Real.sqrt (rho : ℝ) := by
  have hmune : mu ≠ 0 := ne_of_gt hmu
  have hx : (0 : ℝ) < 1 / (2 * mu) := by positivity
  refine ⟨max 1 (Nat.ceil ((1 / (2 * mu)) ^ 2)), ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.one_pos (le_max_left 1 _)
  · have hceil : (1 / (2 * mu)) ^ 2 ≤
        ((Nat.ceil ((1 / (2 * mu)) ^ 2) : ℕ) : ℝ) := Nat.le_ceil _
    have hmono : ((Nat.ceil ((1 / (2 * mu)) ^ 2) : ℕ) : ℝ) ≤
        ((max 1 (Nat.ceil ((1 / (2 * mu)) ^ 2)) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.le_max_right 1 (Nat.ceil ((1 / (2 * mu)) ^ 2)))
    have hsqrt : 1 / (2 * mu) ≤
        Real.sqrt ((max 1 (Nat.ceil ((1 / (2 * mu)) ^ 2)) : ℕ) : ℝ) :=
      (Real.le_sqrt' hx).mpr (le_trans hceil hmono)
    have h2mu : (0 : ℝ) ≤ 2 * mu := by positivity
    have hmul : 2 * mu * (1 / (2 * mu)) ≤
        2 * mu * Real.sqrt ((max 1 (Nat.ceil ((1 / (2 * mu)) ^ 2)) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt h2mu
    have hone : 2 * mu * (1 / (2 * mu)) = 1 := by field_simp
    rw [hone] at hmul
    exact hmul

/-! ## The cell-boundary counting identity -/

/-- Exterior, interior and unbound darts split every relator-cell perimeter,
so the diagram total of the unbound darts is the total perimeter minus the
total of the exterior and interior arcs.  This is the counting step behind
the sum `S` of Osin's Lemma 62. -/
theorem unboundTotal_add_covered_eq_perimeterTotal
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta) :
    (∑ i : Fin Delta.rCellCount,
        ((scaffold.partition i).kindLength Embedded.CellArcKind.exterior +
          (scaffold.partition i).kindLength Embedded.CellArcKind.interior)) +
        scaffold.partition.unboundTotal =
      ∑ i : Fin Delta.rCellCount, (Embedded.cell Delta i).word.length := by
  simp only [Embedded.DiagramBoundaryPartition.unboundTotal]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact ((scaffold.partition i).perimeter_eq_kindLengths).symm

/-! ## The repaired statement -/

/-- Osin Appendix Lemma 62 with the three hypotheses the source states and
`EstimatingUnboundConstructionStatement` drops: the diagram has a relator
cell, the estimating graph satisfies `(*)`, and `rho` was chosen against
`mu`. -/
def EstimatingUnboundRepairedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (_hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ))
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (_hcells : 0 < Delta.rCellCount)
    (scaffold : EstimatingScaffold D eps Delta)
    (_graph : EstimatingGraphData D eps Delta scaffold),
    IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      Nonempty (Lemma62Data D eps mu rho Delta scaffold)

/-- The geometric core of Osin Appendix Lemma 62: cutting off the relator
cells and the distinguished contiguity subdiagrams leaves complementary
components carrying a Lemma 62 averaging certificate at the parameter
`t = sqrt rho`.  Its arc-count field is Lemma 61 and its density field is the
contradiction argument of Lemma 62. -/
def Lemma62ComponentPartitionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (_hsqrt : 0 < Real.sqrt (rho : ℝ))
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (_hcells : 0 < Delta.rCellCount)
    (scaffold : EstimatingScaffold D eps Delta)
    (_graph : EstimatingGraphData D eps Delta scaffold),
    IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      ∃ d : ℕ, Nonempty (PartitionUnboundCertificate Delta.rCellCount d
        (Real.sqrt (rho : ℝ)) (scaffold.partition.unboundTotal : ℝ))

/-- The component partition producer is the whole remaining content of the
repaired statement: the averaging inequality and the numerical threshold are
already proved. -/
theorem estimatingUnboundRepaired_of_componentPartition
    (hpartition : Lemma62ComponentPartitionStatement.{u, w, v}) :
    EstimatingUnboundRepairedStatement.{u, w, v} := by
  intro G _ Lambda D eps rho mu lambda c hthreshold W hcondition Delta hcells
    scaffold graph hboundary
  have hsqrt : 0 < Real.sqrt (rho : ℝ) := sqrt_pos_of_threshold hthreshold
  obtain ⟨d, hcertificate⟩ := hpartition D eps rho mu lambda c hsqrt hcondition
    Delta hcells scaffold graph hboundary
  obtain ⟨certificate⟩ := hcertificate
  exact lemma62Data_of_partitionCertificate certificate hthreshold

/-! ## Model checks -/

/-- The refuting model fails exactly the new cell-count binder, so the repair
is the smallest one that removes it. -/
theorem emptyFamilyDisc_not_rCellCount_pos {G : Type} [Group G]
    {Lambda : Type} (lam : Lambda) :
    ¬ 0 < (emptyFamilyDisc (G := G) (Lambda := Lambda) lam).rCellCount := by
  rw [emptyFamilyDisc_rCellCount]
  exact lt_irrefl 0

/-- A diagram whose selected family covers every relator-cell dart has the
empty component partition, at any positive cell count.  This is the model
check for the target of `Lemma62ComponentPartitionStatement`. -/
theorem partitionCertificate_of_unboundTotal_zero
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (hcells : 0 < Delta.rCellCount)
    (hsqrt : 0 < Real.sqrt (rho : ℝ))
    (hzero : scaffold.partition.unboundTotal = 0) :
    Nonempty (PartitionUnboundCertificate Delta.rCellCount 0
      (Real.sqrt (rho : ℝ)) (scaffold.partition.unboundTotal : ℝ)) := by
  refine ⟨{
    averaging := {
      n_pos := hcells
      t_pos := hsqrt
      arcCount := fun i => Fin.elim0 i
      unboundLength := fun i => Fin.elim0 i
      arc_count_le := by simp
      component_lt := fun i => Fin.elim0 i }
    total_eq := ?_ }⟩
  rw [hzero, Nat.cast_zero]
  simp

/-- With every relator-cell dart covered, the repaired statement's conclusion
holds outright.  This is the case the current statement gets wrong: it also
claims the strict budget when there is no relator cell at all. -/
theorem lemma62Data_of_unboundTotal_zero
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (hcells : 0 < Delta.rCellCount)
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ))
    (hzero : scaffold.partition.unboundTotal = 0) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  have hsqrt : 0 < Real.sqrt (rho : ℝ) := sqrt_pos_of_threshold hthreshold
  obtain ⟨certificate⟩ :=
    partitionCertificate_of_unboundTotal_zero hcells hsqrt hzero
  exact lemma62Data_of_partitionCertificate certificate hthreshold

/-- The averaging parameter of the component partition is the one Osin uses,
and it is positive exactly when the threshold holds. -/
theorem sqrt_pos_iff_threshold_model :
    (0 : ℝ) < Real.sqrt ((1 : ℕ) : ℝ) ∧ (1 : ℝ) ≤ 2 * 1 * Real.sqrt ((1 : ℕ) : ℝ) := by
  rw [Nat.cast_one, Real.sqrt_one]
  constructor
  · exact one_pos
  · norm_num

end Estimating
end VanKampen
end GGT
end GroupApproximation
