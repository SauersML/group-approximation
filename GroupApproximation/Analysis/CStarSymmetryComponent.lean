import GroupApproximation.Analysis.CStarUnitaryComponent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Star.StarProjection

/-!
# Every self-adjoint unitary lies in the identity component

A *symmetry* of a unital C-star algebra is a self-adjoint unitary `u`.  Equivalently
`u = 1 - 2p` for the star projection `p = (1 - u)/2`.  This file proves that every symmetry
lies in `U_0`, by exhibiting the path

    t ↦ 1 + (e^{iπt} - 1) p

of unitaries from `1` to `1 - 2p`.  Nothing here uses the exponential of an algebra element or
the continuous functional calculus: for a projection `p` the element `1 + (z - 1) p` is unitary
whenever `|z| = 1`, by the single identity

    (1 + w p)(1 + v p) = 1 + (w + v + w v) p,

and rotating `z` around the circle from `1` to `-1` is the path.

The consumer is the Whitehead-lemma argument for `K_1`: the block-swap permutation matrix of
`M_{n+n}(A)` is a symmetry, so it lies in `U_0` and therefore acts trivially on
`U(M_{n+n}(A))/U_0(M_{n+n}(A))`.
-/

namespace GroupApproximation

variable {C : Type*} [CStarAlgebra C]

section Algebraic

variable {p : C}

/-- The multiplication rule for the elements `1 + w p` attached to an idempotent `p`. -/
theorem mul_one_add_smul (hpp : p * p = p) (w v : ℂ) :
    ((1 : C) + w • p) * ((1 : C) + v • p) = 1 + (w + v + w * v) • p := by
  have e₀ : ((1 : C) + w • p) * ((1 : C) + v • p)
      = 1 * 1 + 1 * (v • p) + ((w • p) * 1 + (w • p) * (v • p)) := by
    rw [add_mul, mul_add, mul_add]
  have e₁ : (w • p) * (v • p) = (w * v) • p := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hpp]
  rw [e₀, e₁, one_mul, one_mul, mul_one, add_smul, add_smul]
  abel

theorem star_one_add_smul (hps : star p = p) (w : ℂ) :
    star ((1 : C) + w • p) = 1 + (star w) • p := by
  rw [star_add, star_one, star_smul, hps]

/-- For a star projection `p` and a unimodular scalar `z`, the element `1 + (z - 1) p` is a
unitary: it is `z` on the range of `p` and `1` on its kernel. -/
theorem one_add_smul_sub_one_mem_unitary (hp : IsStarProjection p) {z : ℂ}
    (hz : star z * z = 1) : (1 : C) + (z - 1) • p ∈ unitary C := by
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hz' : z * star z = 1 := by rw [mul_comm]; exact hz
  refine ⟨?_, ?_⟩
  · rw [star_one_add_smul hps, star_sub, star_one, mul_one_add_smul hpp,
      show star z - 1 + (z - 1) + (star z - 1) * (z - 1) = 0 by linear_combination hz,
      zero_smul, add_zero]
  · rw [star_one_add_smul hps, star_sub, star_one, mul_one_add_smul hpp,
      show z - 1 + (star z - 1) + (z - 1) * (star z - 1) = 0 by linear_combination hz',
      zero_smul, add_zero]

/-- `1 - 2p` is a unitary for every star projection `p`. -/
theorem one_sub_two_smul_mem_unitary (hp : IsStarProjection p) :
    (1 : C) - (2 : ℂ) • p ∈ unitary C := by
  have h := one_add_smul_sub_one_mem_unitary (C := C) hp (z := -1) (by simp)
  rwa [show ((-1 : ℂ) - 1) = -(2 : ℂ) by norm_num, neg_smul, ← sub_eq_add_neg] at h

/-- If `u` is a self-adjoint unitary then `(1 - u)/2` is a star projection. -/
theorem isStarProjection_half_one_sub {u : C} (hu : IsSelfAdjoint u) (hu2 : u * u = 1) :
    IsStarProjection ((2⁻¹ : ℂ) • ((1 : C) - u)) := by
  have hsq : ((1 : C) - u) * ((1 : C) - u) = ((1 : C) - u) + ((1 : C) - u) := by
    have expand : ((1 : C) - u) * ((1 : C) - u) = 1 - u - u + u * u := by noncomm_ring
    rw [expand, hu2]
    abel
  refine ⟨?_, ?_⟩
  · show (2⁻¹ : ℂ) • ((1 : C) - u) * ((2⁻¹ : ℂ) • ((1 : C) - u)) = (2⁻¹ : ℂ) • ((1 : C) - u)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hsq, smul_add, ← add_smul]
    congr 1
    norm_num
  · show star ((2⁻¹ : ℂ) • ((1 : C) - u)) = (2⁻¹ : ℂ) • ((1 : C) - u)
    rw [star_smul, star_sub, star_one, hu.star_eq]
    norm_num

end Algebraic

section Path

variable {p : C}

theorem star_mul_self_exp (t : ℝ) :
    star (Complex.exp ((t : ℂ) * (Real.pi : ℂ) * Complex.I))
      * Complex.exp ((t : ℂ) * (Real.pi : ℂ) * Complex.I) = 1 := by
  have harg : (starRingEnd ℂ) ((t : ℂ) * (Real.pi : ℂ) * Complex.I)
      + (t : ℂ) * (Real.pi : ℂ) * Complex.I = 0 := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  show (starRingEnd ℂ) (Complex.exp ((t : ℂ) * (Real.pi : ℂ) * Complex.I))
      * Complex.exp ((t : ℂ) * (Real.pi : ℂ) * Complex.I) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add, harg, Complex.exp_zero]

/-- `t ↦ 1 + (e^{iπt} - 1) p` as a family of unitaries. -/
noncomputable def circleUnitary (hp : IsStarProjection p) (t : ℝ) : unitary C :=
  ⟨1 + (Complex.exp ((t : ℂ) * (Real.pi : ℂ) * Complex.I) - 1) • p,
    one_add_smul_sub_one_mem_unitary hp (star_mul_self_exp t)⟩

theorem coe_circleUnitary (hp : IsStarProjection p) (t : ℝ) :
    ((circleUnitary hp t : unitary C) : C)
      = 1 + (Complex.exp ((t : ℂ) * (Real.pi : ℂ) * Complex.I) - 1) • p := rfl

theorem continuous_circleUnitary (hp : IsStarProjection p) :
    Continuous (circleUnitary hp) := by
  refine continuous_induced_rng.mpr ?_
  exact continuous_const.add
    (((Complex.continuous_exp.comp (by fun_prop)).sub continuous_const).smul continuous_const)

theorem circleUnitary_zero (hp : IsStarProjection p) : circleUnitary hp 0 = 1 := by
  refine Subtype.ext ?_
  rw [coe_circleUnitary]
  norm_num

theorem circleUnitary_one (hp : IsStarProjection p) :
    ((circleUnitary hp 1 : unitary C) : C) = 1 - (2 : ℂ) • p := by
  rw [coe_circleUnitary, Complex.ofReal_one, one_mul, Complex.exp_pi_mul_I,
    show ((-1 : ℂ) - 1) = -(2 : ℂ) by norm_num, neg_smul, ← sub_eq_add_neg]

/-- **A symmetry lies in the identity component.**  For a star projection `p`, the unitary
`1 - 2p` is joined to `1` by the path `t ↦ 1 + (e^{iπt} - 1) p`. -/
theorem mem_unitaryComponentOne_of_eq_one_sub_two_smul {u : unitary C} (hp : IsStarProjection p)
    (hup : (u : C) = 1 - (2 : ℂ) • p) : u ∈ unitaryComponentOne C := by
  have hend : circleUnitary hp 1 = u :=
    Subtype.ext ((circleUnitary_one hp).trans hup.symm)
  exact ⟨{ toFun := fun t => circleUnitary hp (t : ℝ)
           continuous_toFun := (continuous_circleUnitary hp).comp continuous_subtype_val
           source' := by simpa using circleUnitary_zero hp
           target' := by simpa using hend }⟩

/-- **Every self-adjoint unitary lies in the identity component of the unitary group.** -/
theorem mem_unitaryComponentOne_of_isSelfAdjoint {u : unitary C} (hu : IsSelfAdjoint (u : C)) :
    u ∈ unitaryComponentOne C := by
  have hu2 : (u : C) * (u : C) = 1 := by
    have h1 : star (u : C) * (u : C) = 1 := u.2.1
    rwa [hu.star_eq] at h1
  refine mem_unitaryComponentOne_of_eq_one_sub_two_smul
    (isStarProjection_half_one_sub hu hu2) ?_
  rw [smul_smul]
  norm_num

end Path

end GroupApproximation
