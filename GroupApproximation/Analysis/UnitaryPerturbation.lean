import GroupApproximation.Analysis.CayleyUnitary
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Perturbing a unitary off the eigenvalue `-1`

The Cayley transform reaches exactly the unitaries `U` for which `1 + U` is
invertible.  Density in the whole unitary group therefore needs an arbitrary
unitary moved slightly onto that set, and rotating by a scalar of modulus one
does it: `1 + lam • U` is singular only when `-lam⁻¹` is a root of the
characteristic polynomial of `U`, and a nonzero polynomial has finitely many
roots.

The scalars used are

    circlePoint m = (m + I) / (m - I),

which have modulus one because `m + I` and `m - I` are conjugate, are pairwise
distinct, and satisfy `‖circlePoint m - 1‖ ≤ 2 / m`.  No exponential and no
continuity argument is needed: an infinite family converging to `1` is written
down directly, and all but finitely many of its members avoid the bad set.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace UnitaryPerturbation

open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Points of the unit circle converging to one -/

/-- Unit-modulus scalars converging to `1`. -/
noncomputable def circlePoint (m : ℕ) : ℂ :=
  ((m : ℂ) + Complex.I) / ((m : ℂ) - Complex.I)

theorem sub_I_ne_zero (m : ℕ) : (m : ℂ) - Complex.I ≠ 0 := by
  intro h
  have him : ((m : ℂ) - Complex.I).im = 0 := by rw [h]; simp
  simp at him

theorem star_sub_I (m : ℕ) : star ((m : ℂ) - Complex.I) = (m : ℂ) + Complex.I := by
  simp

theorem norm_circlePoint (m : ℕ) : ‖circlePoint m‖ = 1 := by
  have hden := sub_I_ne_zero m
  have hnum : ‖(m : ℂ) + Complex.I‖ = ‖(m : ℂ) - Complex.I‖ := by
    rw [← star_sub_I m, norm_star]
  rw [circlePoint, norm_div, hnum, div_self (norm_ne_zero_iff.2 hden)]

theorem circlePoint_ne_zero (m : ℕ) : circlePoint m ≠ 0 := by
  intro h
  have := norm_circlePoint m
  rw [h, norm_zero] at this
  norm_num at this

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro a b hab
  have ha := sub_I_ne_zero a
  have hb := sub_I_ne_zero b
  rw [circlePoint, circlePoint, div_eq_div_iff ha hb] at hab
  have hexp : ((a : ℂ) + Complex.I) * ((b : ℂ) - Complex.I)
      - ((b : ℂ) + Complex.I) * ((a : ℂ) - Complex.I)
      = 2 * Complex.I * ((b : ℂ) - (a : ℂ)) := by ring
  have hzero : (2 : ℂ) * Complex.I * ((b : ℂ) - (a : ℂ)) = 0 := by
    rw [← hexp, hab, sub_self]
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  have hba : (b : ℂ) - (a : ℂ) = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h hI
    · exact h
  have hcast : (a : ℂ) = (b : ℂ) := by linear_combination -hba
  exact_mod_cast hcast

theorem norm_circlePoint_sub_one_le {m : ℕ} (hm : 0 < m) :
    ‖circlePoint m - 1‖ ≤ 2 / (m : ℝ) := by
  have hden := sub_I_ne_zero m
  have hre : (m : ℝ) ≤ ‖(m : ℂ) - Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((m : ℂ) - Complex.I)
    have hval : ((m : ℂ) - Complex.I).re = (m : ℝ) := by simp
    rw [hval, abs_of_nonneg (Nat.cast_nonneg m)] at h
    exact h
  have hsub : circlePoint m - 1 = (2 * Complex.I) / ((m : ℂ) - Complex.I) := by
    rw [circlePoint, div_sub_one hden]
    congr 1
    ring
  rw [hsub, norm_div, show ‖(2 : ℂ) * Complex.I‖ = 2 by simp]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  gcongr

/-! ## The rotations that fail -/

/-- The determinant of `1 + lam • U`, through the characteristic polynomial. -/
theorem det_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) {lam : ℂ} (hlam : lam ≠ 0) :
    ((1 : Matrix n n ℂ) + lam • U).det
      = lam ^ Fintype.card n * ((-1) ^ Fintype.card n
        * U.charpoly.eval (-lam⁻¹)) := by
  have hsc : Matrix.scalar n (-lam⁻¹) = (-lam⁻¹) • (1 : Matrix n n ℂ) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hfac : (1 : Matrix n n ℂ) + lam • U
      = lam • (U - Matrix.scalar n (-lam⁻¹)) := by
    rw [hsc, smul_sub, smul_smul]
    have hval : lam * -lam⁻¹ = (-1 : ℂ) := by field_simp
    rw [hval, neg_one_smul]
    abel
  have hneg : (U - Matrix.scalar n (-lam⁻¹)).det
      = (-1) ^ Fintype.card n * (Matrix.scalar n (-lam⁻¹) - U).det := by
    rw [← Matrix.det_neg, neg_sub]
  rw [hfac, Matrix.det_smul, hneg, Matrix.eval_charpoly]

/-- Only finitely many rotations are bad. -/
theorem finite_bad {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) :
    {lam : ℂ | lam ≠ 0 ∧ ¬ IsUnit ((1 : Matrix n n ℂ) + lam • U).det}.Finite := by
  have hne : U.charpoly ≠ 0 := (Matrix.charpoly_monic U).ne_zero
  have hroots := Polynomial.finite_setOf_isRoot hne
  refine Set.Finite.of_finite_image (f := fun lam : ℂ => -lam⁻¹) ?_ ?_
  · refine hroots.subset ?_
    rintro x ⟨lam, ⟨hlam, hbad⟩, rfl⟩
    have hzero : ((1 : Matrix n n ℂ) + lam • U).det = 0 := by
      rcases eq_or_ne ((1 : Matrix n n ℂ) + lam • U).det 0 with h | h
      · exact h
      · exact absurd (isUnit_iff_ne_zero.2 h) hbad
    rw [det_one_add_smul U hlam] at hzero
    have hlp : lam ^ Fintype.card n ≠ 0 := pow_ne_zero _ hlam
    have hsign : ((-1 : ℂ)) ^ Fintype.card n ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have h1 := (mul_eq_zero.1 hzero).resolve_left hlp
    exact (mul_eq_zero.1 h1).resolve_left hsign
  · intro a ha b hb hab
    have : a⁻¹ = b⁻¹ := by
      have := congrArg Neg.neg hab
      simpa using this
    exact inv_injective this

/-! ## Density of the unitaries without eigenvalue `-1` -/

/-- A unit-modulus multiple of a unitary is unitary. -/
theorem smul_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {c : ℂ} (hc : ‖c‖ = 1) {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : c • U ∈ Matrix.unitaryGroup n ℂ := by
  have hstar : star c * c = 1 := by
    have h2 : Complex.normSq c = 1 := by
      rw [Complex.normSq_eq_norm_sq, hc]; norm_num
    have h1 : ((Complex.normSq c : ℝ) : ℂ) = (starRingEnd ℂ) c * c :=
      Complex.normSq_eq_conj_mul_self
    rw [RCLike.star_def, ← h1, h2]
    norm_num
  refine Matrix.mem_unitaryGroup_iff'.2 ?_
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hstar, one_smul]
  exact Matrix.mem_unitaryGroup_iff'.1 hU

/-- **A unitary can be moved slightly onto the range of the Cayley
transform.** -/
theorem exists_unitary_isUnit_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ Matrix.unitaryGroup n ℂ, ‖U - V‖ < ε ∧
      IsUnit ((1 : Matrix n n ℂ) + V).det := by
  classical
  set bad : Set ℂ :=
    {lam : ℂ | lam ≠ 0 ∧ ¬ IsUnit ((1 : Matrix n n ℂ) + lam • U).det} with hbad
  have hfin : (circlePoint ⁻¹' bad).Finite :=
    Set.Finite.preimage (circlePoint_injective.injOn) (finite_bad U)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  set m : ℕ := max (N + 1) (M + 1) with hm
  have hmpos : 0 < m := by
    rw [hm]; omega
  have hgood : circlePoint m ∉ bad := by
    intro hmem
    have : m ∈ circlePoint ⁻¹' bad := hmem
    have hle : m ≤ N := hN this
    rw [hm] at hle
    omega
  have hunit : IsUnit ((1 : Matrix n n ℂ) + circlePoint m • U).det := by
    by_contra hcon
    exact hgood ⟨circlePoint_ne_zero m, hcon⟩
  refine ⟨circlePoint m • U, smul_mem_unitaryGroup (norm_circlePoint m) hU, ?_,
    hunit⟩
  have hdiff : U - circlePoint m • U = (1 - circlePoint m) • U := by
    rw [sub_smul, one_smul]
  have hUnorm := CayleyUnitary.norm_le_one_of_mem_unitaryGroup hU
  have hbound : ‖U - circlePoint m • U‖ ≤ ‖(1 : ℂ) - circlePoint m‖ := by
    rw [hdiff, norm_smul]
    nlinarith [norm_nonneg ((1 : ℂ) - circlePoint m), norm_nonneg U]
  have hsym : ‖(1 : ℂ) - circlePoint m‖ = ‖circlePoint m - 1‖ := norm_sub_rev _ _
  have hsmall := norm_circlePoint_sub_one_le hmpos
  have hmM : (M : ℝ) < (m : ℝ) := by
    have : M < m := by rw [hm]; omega
    exact_mod_cast this
  have hmpos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hfinal : 2 / (m : ℝ) < ε := by
    have h2 : 2 / ε < (m : ℝ) := lt_trans hM hmM
    rw [div_lt_iff₀ hmpos']
    rw [div_lt_iff₀ hε] at h2
    linarith
  calc ‖U - circlePoint m • U‖ ≤ ‖(1 : ℂ) - circlePoint m‖ := hbound
    _ = ‖circlePoint m - 1‖ := hsym
    _ ≤ 2 / (m : ℝ) := hsmall
    _ < ε := hfinal

/-! ## The Cayley image is dense -/

/-- **Every unitary is approximated by the Cayley transform of a Hermitian
matrix.**  The two halves are `UnitaryPerturbation.exists_unitary_isUnit_one_add`,
which moves the unitary onto the range, and `CayleyUnitary.cayley_param`, which
inverts the transform there. -/
theorem exists_hermitian_cayley_close {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Matrix n n ℂ, Matrix.IsHermitian H ∧
      ‖U - CayleyUnitary.cayley H‖ < ε := by
  obtain ⟨V, hV, hclose, hunit⟩ := exists_unitary_isUnit_one_add hU hε
  refine ⟨CayleyUnitary.param V,
    CayleyUnitary.isHermitian_param hV hunit, ?_⟩
  rwa [CayleyUnitary.cayley_param hunit]

end UnitaryPerturbation
end GroupApproximation
