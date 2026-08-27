import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Analysis.MatrixCoronaDedekindFinite

/-!
# Stable finiteness of norm matrix coronas

This module is the exact manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Lemma `lem:stable-finite`.

Positive matrix sizes are represented by finite nonempty index types. The
order relation `p ≤ q` between projections is written in its equivalent
ring form `q * p = p`, which is the form consumed by the comparison theorem.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Matrix

/-- **Lemma `lem:stable-finite`.** Every finite matrix amplification of a norm
matrix corona is finite. In the base corona, equivalent projections cannot be
properly comparable. -/
def NormMatrixCoronaStableFinite : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)],
    (∀ (k : ℕ), 0 < k →
      ∀ v : Matrix (Fin k) (Fin k) (NormMatrixCStarCorona (fun n ↦ X n)),
        star v * v = 1 → v * star v = 1) ∧
    (∀ p q unitary : NormMatrixCStarCorona (fun n ↦ X n),
      IsStarProjection p → IsStarProjection q →
      star unitary * unitary = 1 →
      q = unitary * p * star unitary → q * p = p → p = q)

/-- Closed proof of stable finiteness and projection comparison for every norm
matrix corona. -/
theorem manuscriptNormMatrixCoronaStableFinite :
    NormMatrixCoronaStableFinite := by
  intro X _
  constructor
  · intro k hk v hv
    exact MatrixCoronaFinite.mul_eq_one_symm_matrixCorona
      ⟨⟨0, hk⟩⟩ X hv
  · intro p q unitary hp hq hunitary hconjugate habsorb
    apply dedekindFiniteCStar_eq_of_murrayVonNeumannEquiv_of_absorbs
      hp hq habsorb
    rw [hconjugate]
    exact MurrayVonNeumannEquiv.of_isometry_conjugate hp hunitary

end OneSidedMFRadical
end Manuscript
end GroupApproximation
