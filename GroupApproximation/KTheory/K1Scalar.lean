import GroupApproximation.KTheory.K1Functorial
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# `K_1(ℂ) = 0`

A unitary `u` in a unital C⋆-algebra whose spectrum is finite is the exponential
`exp (i · arg u)` of the selfadjoint element `arg u` given by the continuous functional calculus:
on a finite spectrum every function, in particular `Complex.arg`, is continuous.  So `u` lies in
the identity component `U_0`.  Every complex `n × n` matrix has finite spectrum, hence every unitary
matrix is connected to `1` and `K_1(ℂ)` is trivial.

* `mem_unitaryComponentOne_of_finite_spectrum`: finite spectrum puts a unitary in `U_0`.
* `finite_spectrum_cstarMat_complex`: `M_n(ℂ)` has finite spectra.
* `kOne_complex_eq_one`: `K_1(ℂ) = 0`, for any (necessarily the standard) star order on `ℂ`.
-/

namespace GroupApproximation

section FiniteSpectrum

open Complex NormedSpace selfAdjoint Unitary
open scoped Real

variable {A : Type*} [CStarAlgebra A]

/-- A unitary with finite spectrum is the exponential of its argument.  This is Mathlib's
`expUnitary_argSelfAdjoint` with continuity of `arg` on the spectrum coming from finiteness
instead of from `‖u - 1‖ < 2`. -/
theorem expUnitary_argSelfAdjoint_of_finite_spectrum {u : unitary A}
    (hu : (spectrum ℂ (u : A)).Finite) : expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) := hu.continuousOn arg
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)

/-- **A unitary with finite spectrum lies in the identity component of the unitary group.** -/
theorem mem_unitaryComponentOne_of_finite_spectrum (u : unitary A)
    (hu : (spectrum ℂ (u : A)).Finite) : u ∈ unitaryComponentOne A := by
  rw [← expUnitary_argSelfAdjoint_of_finite_spectrum hu]
  exact expUnitary_mem_unitaryComponentOne _

end FiniteSpectrum

/-- Every complex `n × n` matrix has finite spectrum. -/
theorem finite_spectrum_cstarMat_complex (n : ℕ) (M : CStarMat n ℂ) : (spectrum ℂ M).Finite := by
  let e : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] CStarMat n ℂ := CStarMatrix.ofMatrixStarAlgEquiv
  have h₁ : spectrum ℂ (e (e.symm M)) = spectrum ℂ (e.symm M) := AlgEquiv.spectrum_eq e (e.symm M)
  have h₂ : e (e.symm M) = M := e.apply_symm_apply M
  rw [h₂] at h₁
  rw [h₁]
  exact Matrix.finite_spectrum _

/-- Every unitary complex matrix is connected to `1` inside the unitary group. -/
theorem mem_unitaryComponentOne_cstarMat_complex [PartialOrder ℂ] [StarOrderedRing ℂ] (n : ℕ)
    (v : unitary (CStarMat n ℂ)) : v ∈ unitaryComponentOne (CStarMat n ℂ) :=
  mem_unitaryComponentOne_of_finite_spectrum v (finite_spectrum_cstarMat_complex n _)

/-- **`K_1(ℂ) = 0`.**  The statement quantifies over the star order on `ℂ` (any
`StarOrderedRing` order on `ℂ` is the standard `ComplexOrder`), so it applies whichever
instance is in scope. -/
theorem kOne_complex_eq_one [PartialOrder ℂ] [StarOrderedRing ℂ] (x : KOne ℂ) : x = 1 := by
  obtain ⟨n, y, rfl⟩ := (kOneTower ℂ).exists_iota x
  refine QuotientGroup.induction_on y fun v => ?_
  show (kOneTower ℂ).iota n (QuotientGroup.mk v) = 1
  rw [(QuotientGroup.eq_one_iff v).mpr (mem_unitaryComponentOne_cstarMat_complex n v), map_one]

instance instSubsingletonKOneComplex [PartialOrder ℂ] [StarOrderedRing ℂ] :
    Subsingleton (KOne ℂ) :=
  ⟨fun x y => (kOne_complex_eq_one x).trans (kOne_complex_eq_one y).symm⟩

end GroupApproximation
