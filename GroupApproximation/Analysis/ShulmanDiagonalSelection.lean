import GroupApproximation.Analysis.UltrafilterDiagonalExtraction
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal selection for Shulman's finite-stage estimates

Suppose that each sequence in a countable family converges along `atTop`.
This file selects one strictly increasing subsequence on which the first
`k + 1` sequences are simultaneously within `1 / (k + 1)` of their limits
at stage `k`.  This is the diagonal selection needed after constructing
coordinatewise unitary representatives in the symmetric-double argument.
-/

namespace GroupApproximation
namespace ShulmanDiagonalSelection

open Filter Topology

noncomputable section

/-- A countable family of convergent sequences admits a strictly increasing
subsequence satisfying the usual expanding finite-stage estimates. -/
theorem exists_strictMono_initial_bounds
    {X : Type*} [PseudoMetricSpace X]
    (F : ℕ → ℕ → X) (L : ℕ → X)
    (hF : ∀ i, Tendsto (F i) atTop (nhds (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k i, i ≤ k →
        dist (F i (φ k)) (L i) ≤ (1 : ℝ) / (k + 1) := by
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop,
      ∀ i ∈ Finset.range (k + 1),
        dist (F i n) (L i) < (1 : ℝ) / (k + 1) := by
    intro k
    have hpos : (0 : ℝ) < (1 : ℝ) / (k + 1) := by positivity
    have hall : ∀ i ∈ Finset.range (k + 1),
        ∀ᶠ n in atTop, dist (F i n) (L i) < (1 : ℝ) / (k + 1) :=
      fun i _ ↦ Metric.tendsto_nhds.mp (hF i) _ hpos
    have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k + 1),
        dist (F i n) (L i) < (1 : ℝ) / (k + 1) :=
      (Filter.eventually_all_finset (Finset.range (k + 1))).mpr hall
    exact hev.frequently
  obtain ⟨φ, hφmono, hφ⟩ := extraction_forall_of_frequently hfreq
  refine ⟨φ, hφmono, fun k i hik ↦ ?_⟩
  exact (hφ k i (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))).le

/-- The selected subsequence still converges for every fixed member of the
countable family. -/
theorem tendsto_along_strictMono_initial_bounds
    {X : Type*} [PseudoMetricSpace X]
    (F : ℕ → ℕ → X) (L : ℕ → X)
    (hF : ∀ i, Tendsto (F i) atTop (nhds (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ k i, i ≤ k →
        dist (F i (φ k)) (L i) ≤ (1 : ℝ) / (k + 1)) ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (nhds (L i)) := by
  obtain ⟨φ, hφmono, hφbound⟩ := exists_strictMono_initial_bounds F L hF
  refine ⟨φ, hφmono, hφbound, fun i ↦ ?_⟩
  exact (hF i).comp hφmono.tendsto_atTop

/-- Real-valued specialization used for norms of commutators. -/
theorem exists_strictMono_norm_initial_bounds
    {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → ℕ → E)
    (hf : ∀ i, Tendsto (fun n ↦ ‖f i n‖) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k i, i ≤ k →
        ‖f i (φ k)‖ ≤ (1 : ℝ) / (k + 1) := by
  obtain ⟨φ, hφmono, hφ⟩ :=
    exists_strictMono_initial_bounds
      (fun i n ↦ ‖f i n‖) (fun _ ↦ (0 : ℝ)) hf
  refine ⟨φ, hφmono, fun k i hik ↦ ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using
    hφ k i hik

/-- Closed endpoint for the norm-valued diagonal selection used in the
Shulman compatibility argument. -/
def NormDiagonalSelection : Prop :=
  ∀ {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → ℕ → E),
    (∀ i, Tendsto (fun n ↦ ‖f i n‖) atTop (nhds 0)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ k i, i ≤ k →
          ‖f i (φ k)‖ ≤ (1 : ℝ) / (k + 1)

/-- A single subsequence gives all expanding finite-stage commutator
estimates. -/
theorem normDiagonalSelection : NormDiagonalSelection := by
  intro E _ f hf
  exact exists_strictMono_norm_initial_bounds f hf

end

end ShulmanDiagonalSelection
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanDiagonalSelection.normDiagonalSelection
