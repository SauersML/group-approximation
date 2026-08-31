import GroupApproximation.Analysis.STW22ProbabilitySimplexBauer
import Mathlib.MeasureTheory.Measure.Sub

/-!
# The probability simplex is a Choquet simplex

This file proves the lattice-cone clause omitted from
`STW22ProbabilitySimplexBauer`.  No signed-measure representation theorem is
needed: Mathlib's complete lattice of positive measures supplies binary suprema,
and subtraction of a finite dominated measure supplies the positive difference
which witnesses the cone order.
-/

namespace GroupApproximation
namespace STW22

open MeasureTheory Set

open scoped NNReal ENNReal

noncomputable section

variable {K : Type*} [MeasurableSpace K]

/-- Embed a finite measure into the cone over the probability simplex by
recording its total mass. -/
def finiteMeasureConePoint (μ : FiniteMeasure K) : FiniteMeasure K × ℝ≥0 :=
  (μ, μ.mass)

/-- Every finite measure, together with its mass, belongs to the cone over
probability measures.  At mass zero we use an arbitrary Dirac probability;
otherwise we normalize by the inverse mass. -/
theorem finiteMeasureConePoint_mem [Nonempty K] (μ : FiniteMeasure K) :
    finiteMeasureConePoint μ ∈ coneOver ℝ≥0 (probSimplex K) := by
  by_cases hμ : μ.mass = 0
  · have hzero : μ = 0 := (FiniteMeasure.mass_zero_iff μ).1 hμ
    refine ⟨0, diracFM (Classical.choice inferInstance),
      diracFM_mem_probSimplex _, zero_le, ?_⟩
    simp [finiteMeasureConePoint, hzero]
  · let ν : FiniteMeasure K := μ.mass⁻¹ • μ
    have hν : ν ∈ probSimplex K := by
      rw [mem_probSimplex, mass_smul_eq]
      exact inv_mul_cancel₀ hμ
    refine ⟨μ.mass, ν, hν, zero_le, ?_⟩
    apply Prod.ext
    · dsimp only [ν, finiteMeasureConePoint]
      rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
    · rfl

/-- Conversely every point of the cone is uniquely of the form
`(μ, μ.mass)`. -/
theorem mem_coneOver_probSimplex_iff [Nonempty K]
    (p : FiniteMeasure K × ℝ≥0) :
    p ∈ coneOver ℝ≥0 (probSimplex K) ↔
      ∃ μ : FiniteMeasure K, p = finiteMeasureConePoint μ := by
  constructor
  · rintro ⟨t, μ, hμ, -, rfl⟩
    refine ⟨t • μ, ?_⟩
    apply Prod.ext
    · rfl
    · rw [finiteMeasureConePoint, mass_smul_eq, show μ.mass = 1 from hμ,
        mul_one]
  · rintro ⟨μ, rfl⟩
    exact finiteMeasureConePoint_mem μ

/-- The positive difference of two finite measures, bundled again as a finite
measure. -/
def finiteMeasureDifference (μ ν : FiniteMeasure K) : FiniteMeasure K :=
  ⟨(ν : Measure K) - (μ : Measure K), inferInstance⟩

/-- A binary supremum of finite measures remains finite because it is bounded
by their sum. -/
def finiteMeasureSup (μ ν : FiniteMeasure K) : FiniteMeasure K := by
  let ρ : Measure K := (μ : Measure K) ⊔ (ν : Measure K)
  have hρ : ρ ≤ (μ : Measure K) + (ν : Measure K) := by
    exact sup_le (Measure.le_add_right le_rfl) (Measure.le_add_left le_rfl)
  letI : IsFiniteMeasure ρ := isFiniteMeasure_of_le
    ((μ : Measure K) + (ν : Measure K)) hρ
  exact ⟨ρ, inferInstance⟩

@[simp] theorem finiteMeasureSup_toMeasure (μ ν : FiniteMeasure K) :
    (finiteMeasureSup μ ν : Measure K) =
      (μ : Measure K) ⊔ (ν : Measure K) := rfl

/-- Cone comparison of mass-tagged finite measures is exactly domination of
their underlying measures. -/
theorem coneLE_finiteMeasureConePoint_iff [Nonempty K]
    (μ ν : FiniteMeasure K) :
    coneLE ℝ≥0 (coneOver ℝ≥0 (probSimplex K))
        (finiteMeasureConePoint μ) (finiteMeasureConePoint ν) ↔
      (μ : Measure K) ≤ (ν : Measure K) := by
  constructor
  · rintro ⟨c, hc, heq⟩
    obtain ⟨δ, rfl⟩ := (mem_coneOver_probSimplex_iff c).1 hc
    have hfirst := congrArg Prod.fst heq
    change ν = μ + δ at hfirst
    rw [← hfirst]
    exact Measure.le_add_right le_rfl
  · intro hμν
    let δ := finiteMeasureDifference μ ν
    have hmeasure : (δ : Measure K) + (μ : Measure K) = (ν : Measure K) := by
      exact Measure.sub_add_cancel_of_le hμν
    have hsum : μ + δ = ν := by
      apply FiniteMeasure.toMeasure_injective
      change (μ : Measure K) + (δ : Measure K) = (ν : Measure K)
      simpa [add_comm] using hmeasure
    refine ⟨finiteMeasureConePoint δ, finiteMeasureConePoint_mem δ, ?_⟩
    apply Prod.ext
    · exact hsum.symm
    · change ν.mass = μ.mass + δ.mass
      exact congrArg FiniteMeasure.mass hsum |>.symm

/-- **Unconditional Choquet theorem.**  The probability measures on a nonempty
measurable space form a Choquet simplex in the lattice-cone sense used by the
STW audit. -/
theorem isChoquetSimplex_probSimplex [Nonempty K] :
    IsChoquetSimplex ℝ≥0 (probSimplex K) := by
  intro u hu v hv
  obtain ⟨μ, rfl⟩ := (mem_coneOver_probSimplex_iff u).1 hu
  obtain ⟨ν, rfl⟩ := (mem_coneOver_probSimplex_iff v).1 hv
  let ω := finiteMeasureSup μ ν
  refine ⟨finiteMeasureConePoint ω, finiteMeasureConePoint_mem ω, ?_, ?_, ?_⟩
  · rw [coneLE_finiteMeasureConePoint_iff, finiteMeasureSup_toMeasure]
    exact le_sup_left
  · rw [coneLE_finiteMeasureConePoint_iff, finiteMeasureSup_toMeasure]
    exact le_sup_right
  · intro z hz hμz hνz
    obtain ⟨ζ, rfl⟩ := (mem_coneOver_probSimplex_iff z).1 hz
    rw [coneLE_finiteMeasureConePoint_iff] at hμz hνz ⊢
    rw [finiteMeasureSup_toMeasure]
    exact sup_le hμz hνz

/-- The probability simplex is unconditionally Bauer under the compact
second-countable Hausdorff hypotheses already used to identify its extreme
boundary with the Dirac masses. -/
theorem isBauerSimplex_probSimplex_unconditional
    [Nonempty K] [TopologicalSpace K] [T2Space K]
    [SecondCountableTopology K] [BorelSpace K] [CompactSpace K]
    [HasOuterApproxClosed K] :
    IsBauerSimplex ℝ≥0 (probSimplex K) :=
  ⟨isChoquetSimplex_probSimplex,
    isCompactConvexClosedBoundary_probSimplex⟩

end

end STW22
end GroupApproximation
