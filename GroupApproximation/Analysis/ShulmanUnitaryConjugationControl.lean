import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import GroupApproximation.Analysis.ShulmanDenseCompatibility

/-!
# From finite commutator control to compatible conjugated models

In Shulman's symmetric-double argument, a corrected unitary approximately
commutes with successively longer initial segments of a dense family.  The
second model is obtained from the first by conjugating with that unitary.
This file proves that those finite commutator estimates imply asymptotic
agreement on the whole source algebra.

The commutant-preserving construction of the corrected unitaries is not
assumed or proved here.  The result isolates the unconditional passage from
its finite estimates to the compatibility needed for amalgamated gluing.
-/

namespace GroupApproximation
namespace ShulmanUnitaryConjugationControl

open Filter

noncomputable section

universe u v

variable {C : Type u} {A : Type v}
  [NormedAddCommGroup C] [CStarAlgebra A]

/-- Conjugation by a unitary preserves the C-star norm. -/
theorem norm_star_mul_mul_of_mem_unitary (v a : A) (hv : v ∈ unitary A) :
    ‖star v * a * v‖ = ‖a‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ hv]
  exact CStarRing.norm_mem_unitary_mul a (Unitary.star_mem hv)

/-- The displacement under unitary conjugation is bounded by the
commutator with the conjugating unitary.  In fact the two norms are equal;
the inequality is the form consumed by finite-stage estimates. -/
theorem norm_conjugation_sub_le_norm_commutator
    (v a : A) (hv : v ∈ unitary A) :
    ‖star v * a * v - a‖ ≤ ‖a * v - v * a‖ := by
  have hvstarv : star v * v = 1 := Unitary.star_mul_self_of_mem hv
  have hfactor : star v * a * v - a = star v * (a * v - v * a) := by
    calc
      star v * a * v - a = star v * a * v - (star v * v) * a := by
        rw [hvstarv, one_mul]
      _ = star v * (a * v - v * a) := by noncomm_ring
  rw [hfactor, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hv)]

/-- Expanding finite commutator control on a dense sequence forces a
contractive asymptotically additive model and its unitary conjugate to agree
asymptotically everywhere.  This is the precise interface between Shulman's
commutant-unitary correction and the compatible gluing step. -/
theorem tendsto_conjugation_sub_of_initial_commutator_controls
    (s : ℕ → C) (hs : DenseRange s)
    (φ : ℕ → C → A)
    (hφadd : ∀ x y : C,
      Tendsto (fun n ↦ ‖φ n (x + y) - φ n x - φ n y‖) atTop (nhds 0))
    (hφcontract : ∀ n x, ‖φ n x‖ ≤ ‖x‖)
    (v : ℕ → A) (hv : ∀ n, v n ∈ unitary A)
    (hcomm : ∀ n j, j ≤ n →
      ‖φ n (s j) * v n - v n * φ n (s j)‖ ≤ (1 : ℝ) / (n + 1))
    (x : C) :
    Tendsto (fun n ↦ ‖star (v n) * φ n x * v n - φ n x‖)
      atTop (nhds 0) := by
  apply ShulmanDenseCompatibility.tendsto_norm_sub_of_initial_dense_controls
    s hs (fun n x ↦ star (v n) * φ n x * v n) φ
  · intro a b
    have hnorm : ∀ n,
        ‖star (v n) * φ n (a + b) * v n -
            star (v n) * φ n a * v n - star (v n) * φ n b * v n‖ =
          ‖φ n (a + b) - φ n a - φ n b‖ := by
      intro n
      have hfactor :
          star (v n) * φ n (a + b) * v n -
              star (v n) * φ n a * v n - star (v n) * φ n b * v n =
            star (v n) * (φ n (a + b) - φ n a - φ n b) * v n := by
        noncomm_ring
      rw [hfactor, norm_star_mul_mul_of_mem_unitary _ _ (hv n)]
    simpa only [hnorm] using hφadd a b
  · exact hφadd
  · intro n a
    rw [norm_star_mul_mul_of_mem_unitary _ _ (hv n)]
    exact hφcontract n a
  · exact hφcontract
  · intro n j hj
    exact (norm_conjugation_sub_le_norm_commutator
      (v n) (φ n (s j)) (hv n)).trans (hcomm n j hj)

/-- Closed universal form of the finite-commutator compatibility theorem. -/
def InitialCommutatorControlsForceConjugateCompatibility : Prop :=
  ∀ {C : Type u} {A : Type v}
    [NormedAddCommGroup C] [CStarAlgebra A]
    (s : ℕ → C), DenseRange s →
    ∀ (φ : ℕ → C → A),
      (∀ x y : C,
        Tendsto (fun n ↦ ‖φ n (x + y) - φ n x - φ n y‖) atTop (nhds 0)) →
      (∀ n x, ‖φ n x‖ ≤ ‖x‖) →
      ∀ (v : ℕ → A), (∀ n, v n ∈ unitary A) →
        (∀ n j, j ≤ n →
          ‖φ n (s j) * v n - v n * φ n (s j)‖ ≤ (1 : ℝ) / (n + 1)) →
        ∀ x : C,
          Tendsto (fun n ↦ ‖star (v n) * φ n x * v n - φ n x‖)
            atTop (nhds 0)

/-- Finite commutator estimates force compatibility of a model with its
unitary conjugate. -/
theorem initialCommutatorControlsForceConjugateCompatibility :
    InitialCommutatorControlsForceConjugateCompatibility := by
  intro C A _ _ s hs φ hφadd hφcontract v hv hcomm x
  exact tendsto_conjugation_sub_of_initial_commutator_controls
    s hs φ hφadd hφcontract v hv hcomm x

end

end ShulmanUnitaryConjugationControl
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanUnitaryConjugationControl.initialCommutatorControlsForceConjugateCompatibility
