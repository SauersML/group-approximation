import GroupApproximation.Analysis.LIXPowersAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# The pinch identification for the join power

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3 item 1, last step.
`Analysis/LIXPowersAngle.lean` builds the angle reparametrisation family `A_{j,θ}` and
`Analysis/LIXPowersEH.lean` reduces the Eckmann--Hilton step to
`Powers.PinchIdentification`, the statement that at time `1` the ordered product of the
`k+1` reparametrised copies collapses to a single composite.  This file discharges it.

## The slab arithmetic

Write `φ = arg z` and `a = (k+1)(φ+π)/(2π) ∈ [0, k+1]`.  The point's own slab is

```text
i = slabIndex k φ = min k ⌊a⌋₊
```

and the three facts are, with `angleRaw k j 1 φ = (k+1)(φ+π) − 2πj`:

* `j < i` ⟹ `2π ≤ angleRaw k j 1 φ`, so the clamp saturates high;
* `i < j ≤ k` ⟹ `angleRaw k j 1 φ ≤ 0`, so the clamp saturates low;
* `j = i` ⟹ `0 ≤ angleRaw k i 1 φ ≤ 2π`, so the clamp is inactive.

At both saturations `A_{j,1}` is the wall retraction (`angleRepar_eq_wallRetract`), so the
`k` other factors evaluate `W` at one and the same wall point; on its own slab the factor
is the target.  The `min k` in `slabIndex` matters only at the single point `φ = π`, where
`a = k+1` and `⌊a⌋₊` overshoots; there the upper bound holds with equality.

## The target, and why it carries a sign

The pinch runs from `φ = −π` to `φ = π`, so its basepoint is the *negative* real axis,
while the join power `joinC k z = z^{k+1}/‖z‖^k` fixes the positive one.  The two differ by
the rotation of the plane through `(k+1−1)π = kπ`, i.e. by the scalar `(−1)^k`:

```text
joinCneg k z = (−1)^k · joinC k z
```

`joinCneg` is again modulus-preserving and positively homogeneous, so `joinPowNeg` is again
an `IsRadialMap` and everything in `Analysis/LIXPowersNaturality.lean` applies to it
unchanged; the `k` preimages of a point and their common local orientation are the join
power's, rotated.  Choosing the other convention would move the wall to the positive reals
and cost a change of branch cut, which is the one thing `Complex.arg` makes expensive.

Every statement here was model-tested first (`sp/angle_modeltest.py`, tests F10--F13,
`k ≤ 6`, 3000 samples per `k`, zero violations; F13 confirms the identification genuinely
fails without the wall condition).
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The target with the pinch sign -/

section Target

/-- **The join power, rotated to the pinch basepoint.** -/
def joinCneg (k : ℕ) (z : ℂ) : ℂ := ((-1 : ℂ) ^ k) * joinC k z

theorem norm_joinCneg (k : ℕ) (z : ℂ) : ‖joinCneg k z‖ = ‖z‖ := by
  rw [joinCneg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_joinC]

theorem continuous_joinCneg (k : ℕ) : Continuous (joinCneg k) :=
  continuous_const.mul (continuous_joinC k)

theorem joinCneg_smul {r : ℝ} (hr : 0 ≤ r) (k : ℕ) (z : ℂ) :
    joinCneg k ((r : ℂ) * z) = (r : ℂ) * joinCneg k z := by
  rw [joinCneg, joinCneg, joinC_smul hr]
  ring

end Target

section TargetE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}

/-- **The `ψ_k` the pinch actually hits.** -/
def joinPowNeg (e₁ e₂ : E) (k : ℕ) : E → E := planeSub e₁ e₂ (joinCneg k)

theorem isRadialMap_joinPowNeg (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (k : ℕ) : IsRadialMap (joinPowNeg e₁ e₂ k) :=
  isRadialMap_planeSub h₁ h₂ h₁₂ (continuous_joinCneg k) (norm_joinCneg k)
    (fun _ hr _ => joinCneg_smul hr k _)

end TargetE

/-! ## The slab index -/

section Slab

/-- The angular slab owning the point of argument `φ`, out of the `k + 1` slabs. -/
def slabIndex (k : ℕ) (φ : ℝ) : ℕ := min k ⌊((k : ℝ) + 1) * (φ + Real.pi) / (2 * Real.pi)⌋₊

theorem slabIndex_le (k : ℕ) (φ : ℝ) : slabIndex k φ ≤ k := min_le_left _ _

theorem angleRaw_one (k j : ℕ) (φ : ℝ) :
    angleRaw k j 1 φ = ((k : ℝ) + 1) * (φ + Real.pi) - 2 * Real.pi * j := by
  rw [angleRaw, angleClamp_one]
  ring

/-- The quantity the floor is taken of is nonnegative on `[−π, π]`. -/
theorem slab_arg_nonneg {k : ℕ} {φ : ℝ} (h : -Real.pi ≤ φ) :
    0 ≤ ((k : ℝ) + 1) * (φ + Real.pi) / (2 * Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ φ + Real.pi := by linarith
  have h3 : (0 : ℝ) < 2 * Real.pi := by linarith
  exact div_nonneg (mul_nonneg h1 h2) (le_of_lt h3)

/-- **Below its own slab, the clamp saturates high.** -/
theorem angleRaw_saturate_high {k j : ℕ} {φ : ℝ} (hφ : -Real.pi ≤ φ)
    (hj : j < slabIndex k φ) : 2 * Real.pi ≤ angleRaw k j 1 φ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set a : ℝ := ((k : ℝ) + 1) * (φ + Real.pi) / (2 * Real.pi) with ha
  have hja : j < ⌊a⌋₊ := lt_of_lt_of_le hj (min_le_right _ _)
  have hstep : ((j : ℝ) + 1) ≤ a := by
    have h1 : (j + 1 : ℕ) ≤ ⌊a⌋₊ := hja
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ (⌊a⌋₊ : ℝ) := Nat.cast_le.mpr h1
    have h3 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le (slab_arg_nonneg hφ)
    push_cast at h2
    linarith
  have hmul : 2 * Real.pi * ((j : ℝ) + 1) ≤ ((k : ℝ) + 1) * (φ + Real.pi) := by
    have h4 : 2 * Real.pi * ((j : ℝ) + 1) ≤ 2 * Real.pi * a := by
      have : (0 : ℝ) < 2 * Real.pi := by linarith
      nlinarith [hstep]
    have h5 : 2 * Real.pi * a = ((k : ℝ) + 1) * (φ + Real.pi) := by
      rw [ha]
      field_simp
    linarith
  rw [angleRaw_one]
  linarith

/-- **Above its own slab, the clamp saturates low.** -/
theorem angleRaw_saturate_low {k j : ℕ} {φ : ℝ} (hφ : -Real.pi ≤ φ) (hjk : j ≤ k)
    (hj : slabIndex k φ < j) : angleRaw k j 1 φ ≤ 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set a : ℝ := ((k : ℝ) + 1) * (φ + Real.pi) / (2 * Real.pi) with ha
  have hfk : ⌊a⌋₊ ≤ k := by
    by_contra hcon
    push Not at hcon
    have : slabIndex k φ = k := min_eq_left (le_of_lt hcon)
    omega
  have hi : slabIndex k φ = ⌊a⌋₊ := min_eq_right hfk
  have hja : ⌊a⌋₊ < j := by rw [← hi]; exact hj
  have halt : a < (j : ℝ) := by
    have h1 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
    have h2 : (⌊a⌋₊ : ℝ) + 1 ≤ (j : ℝ) := by
      have hnat : (⌊a⌋₊ + 1 : ℕ) ≤ j := hja
      have hcast : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hnat
      push_cast at hcast
      linarith
    linarith
  have h5 : 2 * Real.pi * a = ((k : ℝ) + 1) * (φ + Real.pi) := by
    rw [ha]
    field_simp
  have : ((k : ℝ) + 1) * (φ + Real.pi) ≤ 2 * Real.pi * (j : ℝ) := by
    have hpos : (0 : ℝ) < 2 * Real.pi := by linarith
    nlinarith [halt]
  rw [angleRaw_one]
  linarith

/-- **On its own slab the clamp is inactive.** -/
theorem angleRaw_slab_mem {k : ℕ} {φ : ℝ} (h1 : -Real.pi ≤ φ) (h2 : φ ≤ Real.pi) :
    0 ≤ angleRaw k (slabIndex k φ) 1 φ ∧
      angleRaw k (slabIndex k φ) 1 φ ≤ 2 * Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set a : ℝ := ((k : ℝ) + 1) * (φ + Real.pi) / (2 * Real.pi) with ha
  have h5 : 2 * Real.pi * a = ((k : ℝ) + 1) * (φ + Real.pi) := by
    rw [ha]
    field_simp
  have hle : ((slabIndex k φ : ℕ) : ℝ) ≤ a := by
    have hmin : slabIndex k φ ≤ ⌊a⌋₊ := min_le_right _ _
    have h6 : ((slabIndex k φ : ℕ) : ℝ) ≤ (⌊a⌋₊ : ℝ) := Nat.cast_le.mpr hmin
    exact le_trans h6 (Nat.floor_le (slab_arg_nonneg h1))
  constructor
  · rw [angleRaw_one]
    have hpos : (0 : ℝ) < 2 * Real.pi := by linarith
    nlinarith [hle]
  · rw [angleRaw_one]
    rcases le_or_gt (⌊a⌋₊) k with hfk | hfk
    · -- the floor did not overshoot
      have hi : slabIndex k φ = ⌊a⌋₊ := min_eq_right hfk
      have hlt : a < ((slabIndex k φ : ℕ) : ℝ) + 1 := by
        rw [hi]
        exact Nat.lt_floor_add_one a
      have hpos : (0 : ℝ) < 2 * Real.pi := by linarith
      nlinarith [hlt]
    · -- the floor overshot: this forces `φ = π`
      have hi : slabIndex k φ = k := min_eq_left (le_of_lt hfk)
      have hak : ((k : ℝ) + 1) ≤ a := by
        have : (k + 1 : ℕ) ≤ ⌊a⌋₊ := hfk
        have h7 : ((k + 1 : ℕ) : ℝ) ≤ (⌊a⌋₊ : ℝ) := Nat.cast_le.mpr this
        have h8 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le (slab_arg_nonneg h1)
        push_cast at h7
        linarith
      have hphi : Real.pi ≤ φ := by
        have hpos : (0 : ℝ) < 2 * Real.pi := by linarith
        nlinarith [hak, h5]
      have hpieq : φ = Real.pi := le_antisymm h2 hphi
      rw [hi, hpieq]
      have : ((k : ℝ) + 1) * (Real.pi + Real.pi) - 2 * Real.pi * (k : ℝ) = 2 * Real.pi := by
        ring
      linarith [this]

end Slab

/-! ## The exponential bridge -/

section Bridge

/-- On its own slab the reparametrised angle differs from `(k+1)φ + kπ` by a multiple of
`2π`, so the two exponentials agree. -/
theorem angleC_slab_eq_joinCneg {k : ℕ} {z : ℂ} (hz : z ≠ 0) :
    angleC k (slabIndex k (Complex.arg z)) 1 z = joinCneg k z := by
  set φ : ℝ := Complex.arg z with hφdef
  set i : ℕ := slabIndex k φ with hidef
  have h1 : -Real.pi ≤ φ := le_of_lt (Complex.neg_pi_lt_arg z)
  have h2 : φ ≤ Real.pi := Complex.arg_le_pi z
  obtain ⟨hlo, hhi⟩ := angleRaw_slab_mem (k := k) h1 h2
  -- the clamp is inactive, so `angleParam` is the raw value minus `π`
  have hparam : angleParam k i 1 φ = ((k : ℝ) + 1) * (φ + Real.pi) - 2 * Real.pi * i
      - Real.pi := by
    rw [angleParam, max_eq_right hlo, min_eq_right hhi, angleRaw_one]
  -- the two angles differ by `-2πi`
  have hdiff : ((k : ℝ) + 1) * (φ + Real.pi) - 2 * Real.pi * i - Real.pi
      = ((k : ℝ) + 1) * φ + (k : ℝ) * Real.pi + (-(i : ℝ)) * (2 * Real.pi) := by
    ring
  have hk : Complex.exp (((k : ℕ) : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I))
      = (-1 : ℂ) ^ k := by
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  have hi2 : Complex.exp ((-((i : ℕ) : ℂ)) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) = 1 := by
    have h := Complex.exp_int_mul_two_pi_mul_I (-(i : ℤ))
    have hcast : ((-(i : ℤ) : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)
        = (-((i : ℕ) : ℂ)) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rwa [hcast] at h
  have hexp : Complex.exp (((angleParam k i 1 φ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((((k : ℝ) + 1) * φ : ℝ) : ℂ) * Complex.I) * ((-1 : ℂ) ^ k) := by
    have hsplit : ((angleParam k i 1 φ : ℝ) : ℂ) * Complex.I
        = ((((k : ℝ) + 1) * φ : ℝ) : ℂ) * Complex.I
          + (((k : ℕ) : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I)
            + (-((i : ℕ) : ℂ)) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) := by
      rw [hparam, hdiff]
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_add, hk, hi2, mul_one]
  -- the target, in polar form
  have hnzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr hz
  have hzp : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((φ : ℝ) : ℂ) * Complex.I) := by
    rw [hφdef]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have hpow : z ^ (k + 1) = ((‖z‖ : ℝ) : ℂ) ^ (k + 1)
      * Complex.exp (((((k : ℝ) + 1) * φ : ℝ) : ℂ) * Complex.I) := by
    have harg : ((k + 1 : ℕ) : ℂ) * ((((φ : ℝ)) : ℂ) * Complex.I)
        = (((((k : ℝ) + 1) * φ : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    conv_lhs => rw [hzp]
    rw [mul_pow, ← Complex.exp_nat_mul, harg]
  have hck : ((‖z‖ ^ k : ℝ) : ℂ) = ((‖z‖ : ℝ) : ℂ) ^ k := by
    push_cast
    ring
  have hpolar : joinCneg k z = ((-1 : ℂ) ^ k) * (((‖z‖ : ℝ) : ℂ)
      * Complex.exp (((((k : ℝ) + 1) * φ : ℝ) : ℂ) * Complex.I)) := by
    rw [joinCneg, joinC, hpow, hck]
    field_simp
    ring
  rw [angleC, ← hφdef, hexp, hpolar]
  ring

end Bridge

/-! ## The pinch identification -/

section Pinch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}
  {n : Type*} [Fintype n] [DecidableEq n] {W : E → Matrix n n ℂ}

/-- **The pinch identification for the join power.**  If the clutching function is the
identity matrix on the wall, the ordered product of the `k + 1` angle reparametrisations at
time `1` is the single composite `W ∘ ψ_k`.

This is the instance of `Powers.PinchIdentification` that
`exists_partialIsometry_pow_pullback` consumes; with it, §1.3 items 1--3 close for the
agreed `ψ_k`. -/
theorem pinchIdentification_angleRepar (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (k : ℕ)
    (hwall : ∀ y : E, ‖y‖ ≤ 1 → W (wallRetract e₁ e₂ y) = 1) :
    PinchIdentification W (angleFam e₁ e₂ k) (joinPowNeg e₁ e₂ k) (k + 1) := by
  intro y hy
  rw [reparProd_congr (P' := fun j θ => angleRepar e₁ e₂ k j θ)
    (fun j hj => by rw [angleFam_of_le e₁ e₂ (Nat.lt_succ_iff.mp hj)])]
  set z : ℂ := planeC e₁ e₂ y with hzdef
  rcases eq_or_ne z 0 with hz | hz
  · -- the point is on the wall already: every factor is the identity of `E`
    have hid : ∀ j : ℕ, angleRepar e₁ e₂ k j 1 y = y := by
      intro j
      rw [angleRepar, planeSub, ← hzdef, hz, angleC_zero]
      simpa [← hzdef, hz] using planeRest_add_planeC e₁ e₂ y
    have hyw : wallRetract e₁ e₂ y = y := by
      rw [wallRetract, planeSub, ← hzdef, hz, wallC, norm_zero]
      simpa [← hzdef, hz] using planeRest_add_planeC e₁ e₂ y
    have hW1 : W y = 1 := by
      have := hwall y (le_of_eq hy)
      rwa [hyw] at this
    have htgt : joinPowNeg e₁ e₂ k y = y := by
      rw [joinPowNeg, planeSub, ← hzdef, hz, joinCneg, joinC_zero, mul_zero]
      simpa [← hzdef, hz] using planeRest_add_planeC e₁ e₂ y
    rw [htgt, hW1]
    exact reparProd_eq_one (fun j _ => by rw [hid j]; exact hW1)
  · -- the generic case: one owning slab, the rest on the wall
    have h1 : -Real.pi ≤ Complex.arg z := le_of_lt (Complex.neg_pi_lt_arg z)
    have hi : slabIndex k (Complex.arg z) < k + 1 :=
      Nat.lt_succ_of_le (slabIndex_le k (Complex.arg z))
    have hother : ∀ j, j < k + 1 → j ≠ slabIndex k (Complex.arg z) →
        W (angleRepar e₁ e₂ k j 1 y) = 1 := by
      intro j hjk hjne
      have hsat : angleParam k j 1 (Complex.arg z) = Real.pi ∨
          angleParam k j 1 (Complex.arg z) = -Real.pi := by
        rcases lt_or_gt_of_ne hjne.symm with hgt | hlt
        · exact Or.inr (angleParam_eq_neg_pi_of_le
            (angleRaw_saturate_low h1 (Nat.lt_succ_iff.mp hjk) hgt))
        · exact Or.inl (angleParam_eq_pi_of_le (angleRaw_saturate_high h1 hlt))
      have := angleRepar_eq_wallRetract e₁ e₂ (k := k) (j := j) (θ := 1) (y := y)
        (by rw [← hzdef]; exact hsat)
      rw [this]
      exact hwall y (le_of_eq hy)
    rw [reparProd_eq_single hi hother]
    congr 1
    rw [angleRepar, joinPowNeg, planeSub, planeSub, ← hzdef, angleC_slab_eq_joinCneg hz]

end Pinch

end

end Powers
end LIX
end GroupApproximation
