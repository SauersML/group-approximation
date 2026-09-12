import GroupApproximation.Analysis.LIXPowersNaturality
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The join power `ψ_k`, as a radial map

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.2 asks for an explicit `k`-fold map
`ψ_k : S^{2n} → S^{2n}` which is `ρ`-invariant for a rotation `ρ` of order `k` and a local
homeomorphism at the `k` preimages of a chosen equatorial point.  This file builds the
lane's proposal -- the **join power** -- and proves the one property the clutching layer
needs from it, `IsRadialMap`.

## The map

Fix an orthonormal pair `e₁, e₂` in a real inner product space `E`, spanning the plane the
rotation turns.  Reading a point `y` through its complex coordinate
`z = ⟪e₁,y⟫ + i⟪e₂,y⟫` in that plane and its component orthogonal to the plane, put

```text
Ψ_k (z, v) = (z^{k+1} / |z|^k, v)
```

(`joinC k` below; the index is shifted so that `k = 0` is the identity and no `1 ≤ k`
side condition is ever carried).  Three facts make this the right choice and all three are
proved here:

* `norm_joinC` -- `|z^{k+1}/|z|^k| = |z|`, so `Ψ_k` **preserves the norm on all of `E`**,
  not merely on the sphere.  Together with positive homogeneity this says `Ψ_k` *is* the
  cone of `ψ_k`, so `Analysis/LIXPowersNaturality.lean` applies verbatim and the
  suspension `Σψ_k` is the chart map `(t, ν) ↦ (t, Ψ_k ∘ ν)` with no bookkeeping.
* `continuous_joinC` -- continuity, the origin included.  The value at `0` is `0` and the
  norm identity squeezes: `‖Ψ_k y − Ψ_k 0‖ = ‖y‖`.  This is the same damping that makes
  `coneMat` continuous at the poles, and it is why the `ρ`-fixed sphere `{z = 0}` costs
  nothing.
* `joinC_smul` -- positive homogeneity.

The `ρ`-invariance `Ψ_k ∘ ρ = Ψ_k` for `ρ (z, v) = (e^{2πi/k} z, v)`, the preimage count,
and the common orientation of the `k` local branches are properties of the *rotation* and
belong with `sp-design`'s Step-C computation; they are model-tested in this session's
scratchpad (`sp/powers_modeltest.py`, tests B1--B7, all passing, including that the `k`
local Jacobians on `S⁴` are all `+k` once the tangent frames are oriented by the ambient
orientation).  Nothing in the powers chain uses them, so nothing here proves them.

## What is *not* here

The reparametrisation family exhibiting `u^k ≃ u ∘ ψ_k` -- the angle family
`A_{j,θ}(z, v) = (|z| e^{i c_{j,θ}(arg z)}, v)` with
`c_{j,θ}(φ) = clamp((1 + θ(k−1))(φ+π) − 2πθj, 0, 2π) − π` -- is model-tested (tests
E1--E9) but not authored: its continuity across the branch cut is the one place
`Complex.arg` has to be handled, and the choice is `sp-design`'s to sign off.  What it
would discharge is `Powers.PinchIdentification`, and the model test says it does so
exactly when the clutching function is `1` on the cut half-disc `{z ∈ ℝ_{≥0}}` (test E5),
and fails for the raw seam generator (test E9).
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The scalar join power -/

section Scalar

/-- **The scalar join power**, `z ↦ z^{k+1}/|z|^k`.  Total: Lean's `0⁻¹ = 0` makes the
value at the origin `0`, which is also the continuous value. -/
def joinC (k : ℕ) (z : ℂ) : ℂ := ((‖z‖ ^ k : ℝ) : ℂ)⁻¹ * z ^ (k + 1)

theorem joinC_zero (k : ℕ) : joinC k 0 = 0 := by
  rw [joinC, zero_pow (Nat.succ_ne_zero k), mul_zero]

theorem joinC_id (z : ℂ) : joinC 0 z = z := by
  rw [joinC, pow_zero, Complex.ofReal_one, inv_one, pow_one, one_mul]

/-- **The join power preserves the modulus.**  This is the whole reason the map extends
radially to `E` and is its own cone. -/
theorem norm_joinC (k : ℕ) (z : ℂ) : ‖joinC k z‖ = ‖z‖ := by
  rcases eq_or_ne z 0 with h | h
  · rw [h, joinC_zero, norm_zero]
  · have hz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hpk : (‖z‖ ^ k : ℝ) ≠ 0 := pow_ne_zero _ hz
    have e1 : ‖((‖z‖ ^ k : ℝ) : ℂ)⁻¹‖ = (‖z‖ ^ k)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg z) k)]
    have e2 : ‖z ^ (k + 1)‖ = ‖z‖ ^ (k + 1) := norm_pow z (k + 1)
    rw [joinC, norm_mul, e1, e2, pow_succ, ← mul_assoc, inv_mul_cancel₀ hpk, one_mul]

theorem continuous_joinC (k : ℕ) : Continuous (joinC k) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rcases eq_or_ne z₀ 0 with h | h
  · subst h
    refine continuousAt_of_norm_le (r := fun z : ℂ => ‖z‖)
      (fun z => le_of_eq (norm_joinC k z)) ?_ (joinC_zero k)
    have h0 := (continuous_norm (E := ℂ)).tendsto (0 : ℂ)
    rwa [norm_zero] at h0
  · have hz : ((‖z₀‖ ^ k : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr h)
    have h1 : ContinuousAt (fun z : ℂ => ((‖z‖ ^ k : ℝ) : ℂ)) z₀ :=
      (Complex.continuous_ofReal.comp (continuous_norm.pow k)).continuousAt
    exact (h1.inv₀ hz).mul ((continuous_pow (k + 1)).continuousAt)

/-- **Positive homogeneity.** -/
theorem joinC_smul {r : ℝ} (hr : 0 ≤ r) (k : ℕ) (z : ℂ) :
    joinC k ((r : ℂ) * z) = (r : ℂ) * joinC k z := by
  rcases eq_or_ne r 0 with h | h
  · rw [h]
    simp [joinC_zero]
  · rcases eq_or_ne z 0 with hz | hz
    · rw [hz, mul_zero, joinC_zero, mul_zero]
    · have hnorm : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      have hrc : ((r : ℝ) : ℂ) ≠ 0 := by
        simpa using h
      have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
        simpa using norm_ne_zero_iff.mpr hz
      rw [joinC, joinC, hnorm]
      push_cast
      field_simp
      ring

end Scalar

/-! ## The complex coordinate on an orthonormal plane -/

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}

/-- The complex coordinate of `y` in the plane spanned by `e₁, e₂`. -/
def planeC (e₁ e₂ : E) (y : E) : ℂ :=
  ((inner ℝ e₁ y : ℝ) : ℂ) + ((inner ℝ e₂ y : ℝ) : ℂ) * Complex.I

/-- The point of the plane with complex coordinate `w`. -/
def planeE (e₁ e₂ : E) (w : ℂ) : E := w.re • e₁ + w.im • e₂

/-- The component of `y` orthogonal to the plane. -/
def planeRest (e₁ e₂ : E) (y : E) : E := y - planeE e₁ e₂ (planeC e₁ e₂ y)

/-- **Substituting a new plane coordinate.**  `planeSub e₁ e₂ f` replaces the complex
coordinate `z` of `y` in the plane by `f z` and leaves the orthogonal component alone. -/
def planeSub (e₁ e₂ : E) (f : ℂ → ℂ) (y : E) : E :=
  planeRest e₁ e₂ y + planeE e₁ e₂ (f (planeC e₁ e₂ y))

theorem planeC_re (e₁ e₂ : E) (y : E) : (planeC e₁ e₂ y).re = inner ℝ e₁ y := by
  simp [planeC]

theorem planeC_im (e₁ e₂ : E) (y : E) : (planeC e₁ e₂ y).im = inner ℝ e₂ y := by
  simp [planeC]

theorem norm_planeC_sq (e₁ e₂ : E) (y : E) :
    ‖planeC e₁ e₂ y‖ ^ 2 = (inner ℝ e₁ y : ℝ) ^ 2 + (inner ℝ e₂ y : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, planeC, Complex.normSq_add_mul_I]

/-- The plane is spanned isometrically: `‖planeE w‖ = ‖w‖`. -/
theorem norm_planeE (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (w : ℂ) : ‖planeE e₁ e₂ w‖ ^ 2 = ‖w‖ ^ 2 := by
  have hcross : inner ℝ (w.re • e₁) (w.im • e₂) = (0 : ℝ) := by
    rw [real_inner_smul_left, real_inner_smul_right, h₁₂, mul_zero, mul_zero]
  have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [planeE, norm_add_sq_real, hcross, norm_smul, norm_smul, h₁, h₂, hw,
    mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

theorem inner_e₁_planeRest (h₁ : ‖e₁‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (y : E) :
    inner ℝ e₁ (planeRest e₁ e₂ y) = (0 : ℝ) := by
  have h11 : inner ℝ e₁ e₁ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h₁, one_pow]
  rw [planeRest, planeE, inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, h11, h₁₂, planeC_re, planeC_im]
  ring

theorem inner_e₂_planeRest (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (y : E) :
    inner ℝ e₂ (planeRest e₁ e₂ y) = (0 : ℝ) := by
  have h22 : inner ℝ e₂ e₂ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h₂, one_pow]
  have h21 : inner ℝ e₂ e₁ = (0 : ℝ) := by rw [real_inner_comm]; exact h₁₂
  rw [planeRest, planeE, inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, h22, h21, planeC_re, planeC_im]
  ring

theorem inner_planeE_planeRest (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (w : ℂ) (y : E) :
    inner ℝ (planeE e₁ e₂ w) (planeRest e₁ e₂ y) = (0 : ℝ) := by
  rw [planeE, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_e₁_planeRest h₁ h₁₂, inner_e₂_planeRest h₂ h₁₂]
  ring

/-- **The Pythagoras step.** -/
theorem norm_planeRest_add_planeE (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (w : ℂ) (y : E) :
    ‖planeRest e₁ e₂ y + planeE e₁ e₂ w‖ ^ 2 = ‖planeRest e₁ e₂ y‖ ^ 2 + ‖w‖ ^ 2 := by
  have hc : inner ℝ (planeRest e₁ e₂ y) (planeE e₁ e₂ w) = (0 : ℝ) := by
    rw [real_inner_comm]
    exact inner_planeE_planeRest h₁ h₂ h₁₂ w y
  rw [norm_add_sq_real, hc, norm_planeE h₁ h₂ h₁₂]
  ring

theorem planeRest_add_planeC (e₁ e₂ : E) (y : E) :
    planeRest e₁ e₂ y + planeE e₁ e₂ (planeC e₁ e₂ y) = y := by
  rw [planeRest]
  abel

/-- **The norm splits.** -/
theorem norm_sq_split (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (y : E) : ‖y‖ ^ 2 = ‖planeRest e₁ e₂ y‖ ^ 2 + ‖planeC e₁ e₂ y‖ ^ 2 := by
  conv_lhs => rw [← planeRest_add_planeC e₁ e₂ y]
  exact norm_planeRest_add_planeE h₁ h₂ h₁₂ _ y

/-- **`planeSub` preserves the norm** whenever the substituted scalar map does. -/
theorem norm_planeSub (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    {f : ℂ → ℂ} (hf : ∀ z : ℂ, ‖f z‖ = ‖z‖) (y : E) :
    ‖planeSub e₁ e₂ f y‖ = ‖y‖ := by
  have hsq : ‖planeSub e₁ e₂ f y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [planeSub, norm_planeRest_add_planeE h₁ h₂ h₁₂, hf,
      ← norm_sq_split h₁ h₂ h₁₂ y]
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

theorem continuous_planeC (e₁ e₂ : E) : Continuous (planeC e₁ e₂) := by
  have h1 : Continuous fun y : E => ((inner ℝ e₁ y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
  have h2 : Continuous fun y : E => ((inner ℝ e₂ y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
  exact h1.add (h2.mul continuous_const)

theorem continuous_planeE (e₁ e₂ : E) : Continuous (planeE e₁ e₂) :=
  (Complex.continuous_re.smul continuous_const).add
    (Complex.continuous_im.smul continuous_const)

theorem continuous_planeSub (e₁ e₂ : E) {f : ℂ → ℂ} (hf : Continuous f) :
    Continuous (planeSub e₁ e₂ f) := by
  have hrest : Continuous (planeRest e₁ e₂) :=
    continuous_id.sub ((continuous_planeE e₁ e₂).comp (continuous_planeC e₁ e₂))
  exact hrest.add ((continuous_planeE e₁ e₂).comp (hf.comp (continuous_planeC e₁ e₂)))

theorem planeC_smul (e₁ e₂ : E) (r : ℝ) (y : E) :
    planeC e₁ e₂ (r • y) = (r : ℂ) * planeC e₁ e₂ y := by
  rw [planeC, planeC, real_inner_smul_right, real_inner_smul_right]
  push_cast
  ring

theorem planeE_smul (e₁ e₂ : E) (r : ℝ) (w : ℂ) :
    planeE e₁ e₂ ((r : ℂ) * w) = r • planeE e₁ e₂ w := by
  have hre : ((r : ℂ) * w).re = r * w.re := by simp [Complex.mul_re]
  have him : ((r : ℂ) * w).im = r * w.im := by simp [Complex.mul_im]
  rw [planeE, planeE, hre, him, smul_add, smul_smul, smul_smul]

theorem planeRest_smul (e₁ e₂ : E) (r : ℝ) (y : E) :
    planeRest e₁ e₂ (r • y) = r • planeRest e₁ e₂ y := by
  rw [planeRest, planeRest, planeC_smul, planeE_smul, smul_sub]

theorem planeSub_smul (e₁ e₂ : E) {f : ℂ → ℂ} {r : ℝ}
    (hf : ∀ z : ℂ, f ((r : ℂ) * z) = (r : ℂ) * f z) (y : E) :
    planeSub e₁ e₂ f (r • y) = r • planeSub e₁ e₂ f y := by
  rw [planeSub, planeSub, planeRest_smul, planeC_smul, hf, planeE_smul, smul_add]

/-- **A plane substitution by a modulus-preserving, positively homogeneous scalar map is a
radial map.**  This is the interface `Analysis/LIXPowersNaturality.lean` consumes. -/
theorem isRadialMap_planeSub (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) {f : ℂ → ℂ} (hfc : Continuous f)
    (hfn : ∀ z : ℂ, ‖f z‖ = ‖z‖)
    (hfs : ∀ r : ℝ, 0 ≤ r → ∀ z : ℂ, f ((r : ℂ) * z) = (r : ℂ) * f z) :
    IsRadialMap (planeSub e₁ e₂ f) where
  continuous := continuous_planeSub e₁ e₂ hfc
  norm_map := norm_planeSub h₁ h₂ h₁₂ hfn
  map_smul := fun r hr y => planeSub_smul e₁ e₂ (hfs r hr) y

end Plane

/-! ## The join power as a radial map -/

section JoinPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}

/-- **The join power `ψ_{k+1}` on `E`**: raise the plane coordinate to the `(k+1)`-st
power, renormalised to keep its modulus, and leave the orthogonal component alone. -/
def joinPow (e₁ e₂ : E) (k : ℕ) : E → E := planeSub e₁ e₂ (joinC k)

/-- **`ψ_k` is a radial map**, hence its own cone, hence usable verbatim in
`Analysis/LIXPowersNaturality.lean`: the suspension `Σψ_k` is `(t, ν) ↦ (t, ψ_k ∘ ν)` and
`clutch (u ∘ ψ_k)` is the pullback of `clutch u`. -/
theorem isRadialMap_joinPow (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (k : ℕ) : IsRadialMap (joinPow e₁ e₂ k) :=
  isRadialMap_planeSub h₁ h₂ h₁₂ (continuous_joinC k) (norm_joinC k)
    (fun _ hr _ => joinC_smul hr k _)

/-- At `k = 0` the join power is the identity, so the `k`-indexed family starts where it
should. -/
theorem joinPow_zero (e₁ e₂ : E) (y : E) : joinPow e₁ e₂ 0 y = y := by
  rw [joinPow, planeSub]
  simp only [joinC_id]
  exact planeRest_add_planeC e₁ e₂ y

end JoinPower

end

end Powers
end LIX
end GroupApproximation
