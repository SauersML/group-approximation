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
  have : z.natAbs + 1 ≤ z.natAbs := by
    simpa only [Int.natAbs_natCast] using hle
  omega

/-- **Integral general linear groups are residually finite.** -/
theorem generalLinearGroup_int_residuallyFinite :
    Group.ResiduallyFinite (GeneralLinearGroup ι ℤ) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hentry : ∃ i j, ((g : Matrix ι ι ℤ) i j - (1 : Matrix ι ι ℤ) i j) ≠ 0 := by
    by_contra h
    push Not at h
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
  have hentrymod :
      ((g : Matrix ι ι ℤ) i j : ZMod m) =
        (1 : Matrix ι ι (ZMod m)) i j := by
    simpa [integralGLReduction, GeneralLinearGroup.map_apply] using hmatrix
  have hcast : (z : ZMod m) = 0 := by
    change
      ((((g : Matrix ι ι ℤ) i j - (1 : Matrix ι ι ℤ) i j : ℤ) : ZMod m) = 0)
    rw [Int.cast_sub, sub_eq_zero]
    exact hentrymod.trans (by simp [Matrix.one_apply])
  exact intCast_zmod_natAbs_add_one_ne_zero (z := z) hij hcast

/-! ## Separation by an odd modulus

The witness needs more than residual finiteness of `GL(ℤ)`: the separating
quotient must also be one in which the compressing matrix `diag(2,2,2,1)`
becomes invertible, so that conjugation by it descends.  Choosing the modulus
`2|z|+1` instead of `|z|+1` keeps the separation and makes the modulus odd,
which is exactly the condition for `2` — hence `det diag(2,2,2,1) = 8` — to be
a unit. -/

/-- A nonzero integer remains nonzero modulo the odd number `2|z|+1`. -/
theorem intCast_zmod_two_mul_natAbs_add_one_ne_zero {z : ℤ} (hz : z ≠ 0) :
    (z : ZMod (2 * z.natAbs + 1)) ≠ 0 := by
  intro hzero
  have hdiv : ((2 * z.natAbs + 1 : ℕ) : ℤ) ∣ z :=
    (CharP.intCast_eq_zero_iff (ZMod (2 * z.natAbs + 1))
      (2 * z.natAbs + 1) z).mp hzero
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hz
  have : 2 * z.natAbs + 1 ≤ z.natAbs := by
    simpa only [Int.natAbs_natCast] using hle
  omega

/-- **Odd-modulus separation.**  Every nonidentity integral matrix is
separated by reduction modulo some odd modulus, presented as `2k+1`. -/
theorem exists_odd_modulus_reduction_ne_one
    {g : GeneralLinearGroup ι ℤ} (hg : g ≠ 1) :
    ∃ k : ℕ, integralGLReduction ι (2 * k + 1) g ≠ 1 := by
  have hentry : ∃ i j, ((g : Matrix ι ι ℤ) i j - (1 : Matrix ι ι ℤ) i j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply Units.ext
    ext i j
    exact sub_eq_zero.mp (h i j)
  obtain ⟨i, j, hij⟩ := hentry
  let z : ℤ := (g : Matrix ι ι ℤ) i j - (1 : Matrix ι ι ℤ) i j
  refine ⟨z.natAbs, ?_⟩
  have hm : NeZero (2 * z.natAbs + 1) := ⟨by omega⟩
  intro heq
  have hmatrix := congrArg
    (fun u : GeneralLinearGroup ι (ZMod (2 * z.natAbs + 1)) ↦
      ((u : Matrix ι ι (ZMod (2 * z.natAbs + 1))) i j)) heq
  have hentrymod :
      ((g : Matrix ι ι ℤ) i j : ZMod (2 * z.natAbs + 1)) =
        (1 : Matrix ι ι (ZMod (2 * z.natAbs + 1))) i j := by
    simpa [integralGLReduction, GeneralLinearGroup.map_apply] using hmatrix
  have hcast : (z : ZMod (2 * z.natAbs + 1)) = 0 := by
    change
      ((((g : Matrix ι ι ℤ) i j - (1 : Matrix ι ι ℤ) i j : ℤ) :
        ZMod (2 * z.natAbs + 1)) = 0)
    rw [Int.cast_sub, sub_eq_zero]
    exact hentrymod.trans (by simp [Matrix.one_apply])
  exact intCast_zmod_two_mul_natAbs_add_one_ne_zero (z := z) hij hcast

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
