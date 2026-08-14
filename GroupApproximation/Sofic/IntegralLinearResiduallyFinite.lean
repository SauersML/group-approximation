import GroupApproximation.Sofic.LEFSofic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Integral linear groups are residually finite

Reduction modulo an element-dependent modulus separates every nonidentity
integral matrix.  This is the exact elementary residual-finiteness input used
for the affine--Clifford witness; no linear-group residual-finiteness theorem
is assumed.
-/

namespace GroupApproximation

open Matrix

universe u

variable (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- Reduction of integral matrices modulo `m`, bundled on unit groups. -/
def integralGLReduction (m : ℕ) :
    GeneralLinearGroup ι ℤ →* GeneralLinearGroup ι (ZMod m) :=
  GeneralLinearGroup.map (Int.castRingHom (ZMod m))

/-- A nonzero integer remains nonzero modulo one more than its absolute
value. -/
theorem intCast_zmod_natAbs_add_one_ne_zero {z : ℤ} (hz : z ≠ 0) :
    (z : ZMod (z.natAbs + 1)) ≠ 0 := by
  intro hzero
  have hdiv : ((z.natAbs + 1 : ℕ) : ℤ) ∣ z :=
    (CharP.intCast_eq_zero_iff (ZMod (z.natAbs + 1))
      (z.natAbs + 1) z).mp hzero
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hz
  have : z.natAbs + 1 ≤ z.natAbs := by simpa using hle
  omega

/-- **Integral general linear groups are residually finite.** -/
theorem generalLinearGroup_int_residuallyFinite :
    Group.ResiduallyFinite (GeneralLinearGroup ι ℤ) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hentry : ∃ i j, ((g : Matrix ι ι ℤ) i j - (1 : Matrix ι ι ℤ) i j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg
    apply Units.ext
    ext i j
    exact sub_eq_zero.mp (h i j)
  obtain ⟨i, j, hij⟩ := hentry
  let z : ℤ := (g : Matrix ι ι ℤ) i j - (1 : Matrix ι ι ℤ) i j
  let m : ℕ := z.natAbs + 1
  have hm : NeZero m := ⟨by simp [m]⟩
  refine ⟨GeneralLinearGroup ι (ZMod m), inferInstance, inferInstance,
    integralGLReduction ι m, ?_⟩
  intro heq
  have hmatrix := congrArg
    (fun u : GeneralLinearGroup ι (ZMod m) ↦
      ((u : Matrix ι ι (ZMod m)) i j)) heq
  have hcast : (z : ZMod m) = 0 := by
    simpa [integralGLReduction, GeneralLinearGroup.map_apply, z] using
      congrArg (fun q : ZMod m ↦ q - (1 : Matrix ι ι (ZMod m)) i j) hmatrix
  exact intCast_zmod_natAbs_add_one_ne_zero (z := z) hij hcast

/-- Consequently every integral general linear group is LEF. -/
theorem generalLinearGroup_int_isLEF :
    IsLEF (GeneralLinearGroup ι ℤ) := by
  letI : Group.ResiduallyFinite (GeneralLinearGroup ι ℤ) :=
    generalLinearGroup_int_residuallyFinite ι
  exact isLEF_of_residuallyFinite

/-- Consequently every integral general linear group is sofic. -/
theorem generalLinearGroup_int_isSofic :
    IsSofic (GeneralLinearGroup ι ℤ) :=
  isSofic_of_isLEF (generalLinearGroup_int_isLEF ι)

end GroupApproximation
