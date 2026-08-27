import GroupApproximation.Analysis.ShulmanDiagonalSelection
import GroupApproximation.Analysis.ShulmanUnitaryConjugationControl
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal conjugation compatibility

Pointwise asymptotic commutation on a countable dense family can be converted
to the expanding finite-stage estimates used in Shulman's symmetric-double
argument.  The selected subsequence preserves the asymptotic algebraic
relations of the original model.
-/

namespace GroupApproximation
namespace ShulmanDiagonalConjugation

open Filter

noncomputable section

universe u v

variable {C : Type u} {A : Type v}
  [NormedAddCommGroup C] [CStarAlgebra A]

/-- Pointwise asymptotic commutation on a dense sequence yields, after one
subsequence, compatibility of a contractive asymptotic model with its unitary
conjugate on every source element. -/
theorem exists_strictMono_conjugate_compatibility
    (s : ℕ → C) (hs : DenseRange s)
    (φ : ℕ → C → A)
    (hφadd : ∀ x y : C,
      Tendsto (fun n ↦ ‖φ n (x + y) - φ n x - φ n y‖) atTop (nhds 0))
    (hφcontract : ∀ n x, ‖φ n x‖ ≤ ‖x‖)
    (v : ℕ → A) (hv : ∀ n, v n ∈ unitary A)
    (hcomm : ∀ j,
      Tendsto (fun n ↦ ‖φ n (s j) * v n - v n * φ n (s j)‖)
        atTop (nhds 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ x : C,
        Tendsto
          (fun n ↦
            ‖star (v (σ n)) * φ (σ n) x * v (σ n) - φ (σ n) x‖)
          atTop (nhds 0) := by
  obtain ⟨σ, hσmono, hσcomm⟩ :=
    ShulmanDiagonalSelection.exists_strictMono_norm_initial_bounds
      (fun j n ↦ φ n (s j) * v n - v n * φ n (s j)) hcomm
  refine ⟨σ, hσmono, fun x ↦ ?_⟩
  exact ShulmanUnitaryConjugationControl.tendsto_conjugation_sub_of_initial_commutator_controls
    s hs (fun n ↦ φ (σ n))
    (fun a b ↦ (hφadd a b).comp hσmono.tendsto_atTop)
    (fun n a ↦ hφcontract (σ n) a)
    (fun n ↦ v (σ n)) (fun n ↦ hv (σ n)) hσcomm x

/-- Closed endpoint for the diagonal conjugation argument. -/
def PointwiseCommutatorsForceSubsequentialCompatibility : Prop :=
  ∀ {C : Type u} {A : Type v}
    [NormedAddCommGroup C] [CStarAlgebra A]
    (s : ℕ → C), DenseRange s →
    ∀ (φ : ℕ → C → A),
      (∀ x y : C,
        Tendsto (fun n ↦ ‖φ n (x + y) - φ n x - φ n y‖) atTop (nhds 0)) →
      (∀ n x, ‖φ n x‖ ≤ ‖x‖) →
      ∀ (v : ℕ → A), (∀ n, v n ∈ unitary A) →
        (∀ j,
          Tendsto (fun n ↦ ‖φ n (s j) * v n - v n * φ n (s j)‖)
            atTop (nhds 0)) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          ∀ x : C,
            Tendsto
              (fun n ↦
                ‖star (v (σ n)) * φ (σ n) x * v (σ n) - φ (σ n) x‖)
              atTop (nhds 0)

/-- Pointwise dense-family commutator convergence forces full compatibility
after a single diagonal subsequence. -/
theorem pointwiseCommutatorsForceSubsequentialCompatibility :
    PointwiseCommutatorsForceSubsequentialCompatibility := by
  intro C A _ _ s hs φ hφadd hφcontract v hv hcomm
  exact exists_strictMono_conjugate_compatibility
    s hs φ hφadd hφcontract v hv hcomm

end


end ShulmanDiagonalConjugation
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanDiagonalConjugation.pointwiseCommutatorsForceSubsequentialCompatibility
