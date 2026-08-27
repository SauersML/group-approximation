import GroupApproximation.Analysis.BlackadarKirchbergConvexSupportDensity
import GroupApproximation.Analysis.CStarStateSeparation
import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Meta.AxiomGuard

/-!
# Scalar coordinate-state density for bounded matrix products

This is the scalar analytic core of finite-coordinate localization.  The
norm of a bounded matrix sequence is approached by one of its coordinates.
For a self-adjoint element, shifting by its norm makes every coordinate
spectrum nonnegative, so a coordinate state can attain the shifted
coordinate norm.  These facts are the support estimate used to approximate a
state on the product by convex combinations of coordinate states.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarState
open scoped Matrix.Norms.L2Operator
open scoped Pointwise

noncomputable section

universe u

variable {X : ℕ → Type u} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

omit [∀ n, Nonempty (X n)] in
/-- A coordinate norm comes within every positive tolerance of the norm of a
bounded matrix sequence. -/
theorem exists_coordinate_norm_add_gt
    (a : BoundedMatrixSequence X) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ n : ℕ, ‖a‖ < ‖a n‖ + delta := by
  by_contra h
  push Not at h
  have hcoord : ∀ n : ℕ, ‖a n‖ ≤ ‖a‖ - delta := by
    intro n
    linarith [h n]
  have hsup : (⨆ n, ‖a n‖) ≤ ‖a‖ - delta := ciSup_le hcoord
  rw [← boundedMatrixSequence_norm_eq_ciSup X a] at hsup
  linarith

section SpectralShift

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Shifting a self-adjoint element by its norm makes its real spectrum
nonnegative. -/
theorem spectrum_add_norm_one_nonneg (h : A)
    (r : ℝ)
    (hr : r ∈ spectrum ℝ (h + ((‖h‖ : ℝ) : ℂ) • (1 : A))) : 0 ≤ r := by
  let c : ℂ := ((‖h‖ : ℝ) : ℂ)
  let y : A := h + c • (1 : A)
  have hrC : (r : ℂ) ∈ spectrum ℂ y := by
    simpa [y, c] using (spectrum.algebraMap_mem ℂ hr)
  have hsub : y - c • (1 : A) = h := by
    simp [y]
  have hshift : spectrum ℂ h = spectrum ℂ y - ({c} : Set ℂ) := by
    rw [← hsub, ← Algebra.algebraMap_eq_smul_one (R := ℂ) (A := A) c]
    exact (spectrum.sub_singleton_eq y c).symm
  have hu : (r : ℂ) - c ∈ spectrum ℂ h := by
    rw [hshift]
    exact ⟨(r : ℂ), hrC, c, Set.mem_singleton c, rfl⟩
  have hubound : ‖(r : ℂ) - c‖ ≤ ‖h‖ :=
    spectrum.norm_le_norm_of_mem hu
  have habs : |r - ‖h‖| ≤ ‖h‖ := by
    have heq : (r : ℂ) - c = ((r - ‖h‖ : ℝ) : ℂ) := by
      simp [c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs] at hubound
    exact hubound
  linarith [abs_le.mp habs |>.1]

/-- More generally, every real shift at least as large as the norm makes the
real spectrum nonnegative. -/
theorem spectrum_add_scalar_one_nonneg (h : A) (c : ℝ) (hc : ‖h‖ ≤ c)
    (r : ℝ) (hr : r ∈ spectrum ℝ (h + (c : ℂ) • (1 : A))) : 0 ≤ r := by
  let z : ℂ := (c : ℂ)
  let y : A := h + z • (1 : A)
  have hrC : (r : ℂ) ∈ spectrum ℂ y := by
    simpa [y, z] using (spectrum.algebraMap_mem ℂ hr)
  have hsub : y - z • (1 : A) = h := by simp [y]
  have hshift : spectrum ℂ h = spectrum ℂ y - ({z} : Set ℂ) := by
    rw [← hsub, ← Algebra.algebraMap_eq_smul_one (R := ℂ) (A := A) z]
    exact (spectrum.sub_singleton_eq y z).symm
  have hu : (r : ℂ) - z ∈ spectrum ℂ h := by
    rw [hshift]
    exact ⟨(r : ℂ), hrC, z, Set.mem_singleton z, rfl⟩
  have hubound : ‖(r : ℂ) - z‖ ≤ ‖h‖ :=
    spectrum.norm_le_norm_of_mem hu
  have habs : |r - c| ≤ ‖h‖ := by
    have heq : (r : ℂ) - z = ((r - c : ℝ) : ℂ) := by simp [z]
    rw [heq, Complex.norm_real, Real.norm_eq_abs] at hubound
    exact hubound
  linarith [abs_le.mp habs |>.1]

/-- A self-adjoint element with nonnegative real spectrum has its norm as a
complex spectral value. -/
theorem norm_mem_spectrum_of_selfAdjoint_of_nonneg
    (y : A) (hy : IsSelfAdjoint y)
    (hspec : ∀ r ∈ spectrum ℝ y, 0 ≤ r) :
    ((‖y‖ : ℝ) : ℂ) ∈ spectrum ℂ y := by
  obtain ⟨z, hz, hznorm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
      (spectrum.nonempty y)
  have hzre : z = z.re := hy.mem_spectrum_eq_re hz
  have hreMem : z.re ∈ spectrum ℝ y := by
    apply spectrum.of_algebraMap_mem (S := ℂ)
    simpa [← hzre] using hz
  have hreNonneg : 0 ≤ z.re := hspec z.re hreMem
  have hznorm' : ‖z‖ = ‖y‖ := by
    have hspectral := hy.spectralRadius_eq_nnnorm
    rw [hspectral] at hznorm
    have hnn : ‖z‖₊ = ‖y‖₊ := by exact_mod_cast hznorm
    exact congrArg NNReal.toReal hnn
  have hzval : z.re = ‖y‖ := by
    have hzabs : ‖z‖ = |z.re| := by
      conv_lhs => rw [hzre]
      exact Complex.norm_real z.re
    rw [hzabs, abs_of_nonneg hreNonneg] at hznorm'
    exact hznorm'
  have hzEq : z = ((‖y‖ : ℝ) : ℂ) := by rw [hzre, hzval]
  rw [← hzEq]
  exact hz

/-- The shifted self-adjoint element has its norm as a spectral value. -/
theorem norm_mem_spectrum_add_norm_one (h : A) (hh : IsSelfAdjoint h) :
    ((‖h + ((‖h‖ : ℝ) : ℂ) • (1 : A)‖ : ℝ) : ℂ) ∈
      spectrum ℂ (h + ((‖h‖ : ℝ) : ℂ) • (1 : A)) := by
  apply norm_mem_spectrum_of_selfAdjoint_of_nonneg
  · exact hh.add (by simp [IsSelfAdjoint])
  · exact spectrum_add_norm_one_nonneg h

/-- A self-adjoint element shifted by any scalar at least its norm has its
norm as a spectral value. -/
theorem norm_mem_spectrum_add_scalar_one (h : A) (hh : IsSelfAdjoint h)
    (c : ℝ) (hc : ‖h‖ ≤ c) :
    ((‖h + (c : ℂ) • (1 : A)‖ : ℝ) : ℂ) ∈
      spectrum ℂ (h + (c : ℂ) • (1 : A)) := by
  apply norm_mem_spectrum_of_selfAdjoint_of_nonneg
  · exact hh.add (by simp [IsSelfAdjoint])
  · exact spectrum_add_scalar_one_nonneg h c hc

end SpectralShift

local instance boundedMatrixSequenceCStarAlgebraForScalarStateDensity :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := by
    constructor
    intro c x
    apply lp.ext
    funext n
    change star (c • x n) = star c • star (x n)
    rw [star_smul]

/-- Every scalar state on the bounded product satisfies the coordinate-state
support inequality, up to an arbitrarily small loss, on a self-adjoint
element. -/
theorem exists_coordinate_state_support_selfAdjoint
    (state : BoundedMatrixSequence X →L[ℂ] ℂ)
    (hstateOne : state 1 = 1) (hstateNorm : ‖state‖ ≤ 1)
    (h : BoundedMatrixSequence X) (hh : IsSelfAdjoint h)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ (n : ℕ) (coordinateState : Matrix (X n) (X n) ℂ →L[ℂ] ℂ),
      coordinateState 1 = 1 ∧ ‖coordinateState‖ ≤ 1 ∧
        (state h).re < (coordinateState (h n)).re + delta := by
  let shifted : BoundedMatrixSequence X :=
    h + ((‖h‖ : ℝ) : ℂ) • (1 : BoundedMatrixSequence X)
  obtain ⟨n, hn⟩ := exists_coordinate_norm_add_gt shifted hdelta
  have hhn : IsSelfAdjoint (h n) := by
    rw [IsSelfAdjoint]
    have hs := hh.star_eq
    exact congrFun (congrArg DFunLike.coe hs) n
  have hcoordBound : ‖h n‖ ≤ ‖h‖ :=
    boundedMatrixSequence_coord_norm_le X h n
  let shiftedCoord : Matrix (X n) (X n) ℂ :=
    h n + ((‖h‖ : ℝ) : ℂ) • 1
  have hspectral : ((‖shiftedCoord‖ : ℝ) : ℂ) ∈
      spectrum ℂ shiftedCoord := by
    exact norm_mem_spectrum_add_scalar_one (h n) hhn ‖h‖ hcoordBound
  obtain ⟨coordinateState, hcoordinateOne, hcoordinateNorm,
      hcoordinateValue⟩ :=
    exists_unitalContraction_apply_eq shiftedCoord hspectral
  refine ⟨n, coordinateState, hcoordinateOne, hcoordinateNorm, ?_⟩
  have hstateShifted :
      state shifted = state h + ((‖h‖ : ℝ) : ℂ) := by
    simp [shifted, hstateOne]
  have hcoordinateShifted :
      coordinateState shiftedCoord =
        coordinateState (h n) + ((‖h‖ : ℝ) : ℂ) := by
    simp [shiftedCoord, hcoordinateOne]
  have hstateUpper : (state shifted).re ≤ ‖shifted‖ := by
    calc
      (state shifted).re ≤ ‖state shifted‖ := Complex.re_le_norm _
      _ ≤ ‖state‖ * ‖shifted‖ := state.le_opNorm shifted
      _ ≤ 1 * ‖shifted‖ := by gcongr
      _ = ‖shifted‖ := one_mul _
  have hcoordEq : shifted n = shiftedCoord := by rfl
  have hnear : ‖shifted‖ < ‖shiftedCoord‖ + delta := by
    simpa [hcoordEq] using hn
  have hcoordNorm : ‖shiftedCoord‖ = (coordinateState shiftedCoord).re := by
    rw [hcoordinateValue]
    simp
  rw [hstateShifted] at hstateUpper
  rw [hcoordNorm, hcoordinateShifted] at hnear
  simp only [map_add, Complex.add_re, Complex.ofReal_re] at hstateUpper hnear
  linarith

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_coordinate_norm_add_gt
#audit_axioms spectrum_add_norm_one_nonneg
#audit_axioms spectrum_add_scalar_one_nonneg
#audit_axioms norm_mem_spectrum_of_selfAdjoint_of_nonneg
#audit_axioms norm_mem_spectrum_add_norm_one
#audit_axioms norm_mem_spectrum_add_scalar_one
#audit_axioms exists_coordinate_state_support_selfAdjoint
