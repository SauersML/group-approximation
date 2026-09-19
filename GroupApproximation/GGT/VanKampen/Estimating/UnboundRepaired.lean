import GroupApproximation.GGT.VanKampen.Estimating.UnboundEmptyDisc

/-!
# The earlier attempted repair of Lemma 62

This file retains the positive-cell and numerical-threshold repair of the
empty-disc failure, together with its valid conditional reductions and
counting lemmas. Its universal geometric producer statements are still
false: `UnboundSmallMuCounterexample` gives closed refutations of both
`EstimatingUnboundRepairedStatement` and `Lemma62ComponentPartitionStatement`.
The counterexample satisfies Cayley hyperbolicity and the source's strict
parameter ranges; epsilon and rho must also be chosen at the geometric
scales omitted here. See issue #198 and `UnboundParameters`.

`exists_rho_threshold` and the partition-to-budget implications below remain
valid. They do not construct a partition certificate for every input.
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

/-- Osin's parameter choice `rho > mu^{-2}` is available at a single `rho`.
The uniform statement over all large `rho` is `exists_two_mu_sqrt_threshold`,
and this is its one-witness corollary, in the shape the selection statement
now promises. -/
theorem exists_rho_threshold {mu : ℝ} (hmu : 0 < mu) :
    ∃ rho : ℕ, 0 < rho ∧ 1 ≤ 2 * mu * Real.sqrt (rho : ℝ) := by
  obtain ⟨rho0, hrho0, hthreshold⟩ := exists_two_mu_sqrt_threshold mu hmu
  exact ⟨rho0, hrho0, hthreshold rho0 (le_refl rho0)⟩

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

/-! ## The retained attempted repair -/

/-- The earlier same-diagram repair, now refuted by
`UnboundSmallMuCounterexample.not_estimatingUnboundRepairedStatement`. -/
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

/-- The attempted universal partition producer, now refuted by
`UnboundSmallMuCounterexample.not_lemma62ComponentPartitionStatement`.
Its intended geometric interpretation was: cutting off the relator
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

/-- The same-diagram form gives the source's `O`-equivalent output form, by
the reflexive `O`-equivalence.  A producer that never has to move the diagram
can be written at this stronger statement. -/
theorem estimatingUnboundOutput_of_repaired
    (hrepaired : EstimatingUnboundRepairedStatement.{u, w, v}) :
    EstimatingUnboundOutputStatement.{u, w, v} := by
  intro G _ Lambda D eps rho mu lambda c hthreshold W hcondition Delta hred
    hcells scaffold graph hboundary
  exact ⟨Delta, ⟨OEquivalentDiscDiagram.refl Delta⟩, hred, scaffold, ⟨graph⟩,
    hrepaired D eps rho mu lambda c hthreshold hcondition Delta hcells scaffold
      graph hboundary⟩

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
