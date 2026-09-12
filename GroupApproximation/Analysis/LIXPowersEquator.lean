import GroupApproximation.Analysis.LIXPowersSphere
import GroupApproximation.Analysis.LIXGenericEquator

/-!
# The join power at the equator of `S^{2n+1}`, and the rank-`n` export

`Analysis/LIXPowersSphere.lean` exports `ũ^{k+1} ≃ ũ ∘ ψ_k` for any sphere unitary and any
orthonormal pair `e₁, e₂`, with `ψ_k = joinPowNeg e₁ e₂ k`.  This file fixes the pair on the
tower's equatorial space `E n = EuclideanSpace ℝ (Fin (2n+1))` and identifies the map with
the `k`-fold map on the `CharClass` side.

## The pair, and why it is negated

Let `ε₀, ε₁` be the standard basis vectors of `E n` at the two real coordinates that
`Gen.equatorEmb n` pairs into the complex coordinate `0` of `ℂ^{n+1}`.  Negating the plane
turns the pinch power into the plain join power (`joinPowNeg_neg_neg`):

```text
joinPowNeg (−ε₀) (−ε₁) k  =  joinPow ε₀ ε₁ k
```

and the plain join power is the `k`-fold map of lane `sp-oddside-n` read through the equator
embedding (`equatorEmb_joinPow`):

```text
Gen.equatorEmb n (joinPow ε₀ ε₁ k a)  =  Function.update (Gen.equatorEmb n a) 0 (joinC k (Gen.equatorEmb n a 0))
```

whose right-hand side is `KGen.psiVec n k (Gen.equatorEmb n a)` by definition.  So the
export with `e₁ := −ε₀`, `e₂ := −ε₁` pulls the frames back along the **same** `Ψ_k` that
`KGen.bVecK n k` substitutes into the section: this is Step A's `hGe`.  For that pair the wall
is the *positive* real axis of the coordinate `x₀` (`wallRetract_neg_neg`).

## Main results

* `joinPowNeg_neg_neg`, `wallRetract_neg_neg` -- negating the plane.
* `eqBasis`, `norm_eqBasis`, `inner_eqBasis_zero_one` -- the pair is orthonormal.
* `equatorEmb_planeSub`, `equatorEmb_joinPow`, `equatorEmb_joinPowNeg_exportPair` -- the
  bridge to `KGen.psiVec`.
* `isRadialMap_joinPow_equator` -- `ψ_k` at the equator is a radial map.
* `isSphereUnitary_genSphere`, `genSphere_joinPow` -- the seam generator.
* `ballWall_genSphere_zero` -- the ball extension of the wall part at the centre.
* `exists_homotopy_pow_comp_genSphere` -- **the rank-`n` export**, with nothing left to
  instantiate.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Negating the plane -/

section Neg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem planeC_neg_neg (e₁ e₂ y : E) : planeC (-e₁) (-e₂) y = -planeC e₁ e₂ y := by
  rw [planeC, planeC, inner_neg_left, inner_neg_left]
  push_cast
  ring

theorem planeE_neg_neg (e₁ e₂ : E) (w : ℂ) : planeE (-e₁) (-e₂) w = planeE e₁ e₂ (-w) := by
  simp only [planeE, Complex.neg_re, Complex.neg_im, smul_neg, neg_smul]

theorem planeRest_neg_neg (e₁ e₂ y : E) : planeRest (-e₁) (-e₂) y = planeRest e₁ e₂ y := by
  rw [planeRest, planeRest, planeC_neg_neg, planeE_neg_neg, neg_neg]

theorem planeSub_neg_neg (e₁ e₂ : E) (f : ℂ → ℂ) (y : E) :
    planeSub (-e₁) (-e₂) f y = planeSub e₁ e₂ (fun z => -f (-z)) y := by
  rw [planeSub, planeSub, planeRest_neg_neg, planeC_neg_neg, planeE_neg_neg]

/-- The pinch power is the join power conjugated by `z ↦ −z`. -/
theorem joinCneg_neg (k : ℕ) (z : ℂ) : joinCneg k (-z) = -joinC k z := by
  have h : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hz : (-z) ^ (k + 1) = (-1) ^ k * (-1) * z ^ (k + 1) := by
    rw [neg_eq_neg_one_mul z, mul_pow, pow_succ (-1 : ℂ) k]
  simp only [joinCneg, joinC, norm_neg, hz]
  linear_combination (-(((‖z‖ ^ k : ℝ) : ℂ)⁻¹ * z ^ (k + 1))) * h

/-- **Negating the plane turns the pinch power into the join power.** -/
theorem joinPowNeg_neg_neg (e₁ e₂ : E) (k : ℕ) :
    joinPowNeg (-e₁) (-e₂) k = joinPow e₁ e₂ k := by
  funext y
  have hf : (fun z : ℂ => -joinCneg k (-z)) = joinC k := by
    funext z
    rw [joinCneg_neg, neg_neg]
  rw [joinPowNeg, joinPow, planeSub_neg_neg, hf]

/-- For the negated pair the wall is the positive real axis of the plane coordinate. -/
theorem wallRetract_neg_neg (e₁ e₂ y : E) :
    wallRetract (-e₁) (-e₂) y = planeSub e₁ e₂ (fun z => ((‖z‖ : ℝ) : ℂ)) y := by
  have hf : (fun z : ℂ => -wallC (-z)) = fun z => ((‖z‖ : ℝ) : ℂ) := by
    funext z
    rw [wallC, norm_neg, neg_neg]
  rw [wallRetract, planeSub_neg_neg, hf]

end Neg

/-! ## The equatorial pair -/

section Equator

variable (n : ℕ) (hn : 0 < n)

/-- The coordinate of `ℝ^{2n+1}` carrying the real (`b = 0`) or imaginary (`b = 1`) part of
the complex coordinate `0` of `ℂ^{n+1}` under `Gen.equatorEmb n`. -/
def eqIdx0 (b : Fin 2) : Fin (2 * n + 1) := Gen.eqFwd n (Sum.inl (⟨0, hn⟩, b))

/-- The standard basis vector of `E n` at `eqIdx0 n hn b`. -/
def eqBasis (b : Fin 2) : EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  EuclideanSpace.single (eqIdx0 n hn b) (1 : ℝ)

theorem eqIdx0_val (b : Fin 2) : ((eqIdx0 n hn b : Fin (2 * n + 1)) : ℕ) = (b : ℕ) := by
  show 2 * ((⟨0, hn⟩ : Fin n) : ℕ) + (b : ℕ) = (b : ℕ)
  simp

theorem eqBasis_apply (b : Fin 2) (j : Fin (2 * n + 1)) :
    eqBasis n hn b j = if j = eqIdx0 n hn b then 1 else 0 := by
  simp only [eqBasis, EuclideanSpace.single, PiLp.single_apply]

theorem norm_eqBasis (b : Fin 2) : ‖eqBasis n hn b‖ = 1 := by
  simp only [eqBasis, EuclideanSpace.single, PiLp.norm_single, norm_one]

theorem inner_eqBasis (b : Fin 2) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    inner ℝ (eqBasis n hn b) a = a (eqIdx0 n hn b) := by
  rw [eqBasis, EuclideanSpace.inner_single_left]
  simp

theorem eqIdx0_ne {b b' : Fin 2} (h : b ≠ b') : eqIdx0 n hn b ≠ eqIdx0 n hn b' := by
  intro he
  have hv := congrArg Fin.val he
  rw [eqIdx0_val, eqIdx0_val] at hv
  exact h (Fin.ext hv)

theorem eqFwd_ne_eqIdx0 {i : Fin n} (hi : i ≠ ⟨0, hn⟩) (b b' : Fin 2) :
    Gen.eqFwd n (Sum.inl (i, b)) ≠ eqIdx0 n hn b' := by
  intro he
  have hv := congrArg Fin.val he
  rw [Gen.eqFwd_inl_val, eqIdx0_val] at hv
  have hb := b.isLt
  have hb' := b'.isLt
  apply hi
  refine Fin.ext ?_
  show (i : ℕ) = 0
  omega

theorem eqFwd_inr_ne_eqIdx0 (b : Fin 2) : Gen.eqFwd n (Sum.inr ()) ≠ eqIdx0 n hn b := by
  intro he
  have hv := congrArg Fin.val he
  rw [Gen.eqFwd_inr_val, eqIdx0_val] at hv
  have hb := b.isLt
  omega

/-- **The pair is orthonormal.** -/
theorem inner_eqBasis_zero_one : inner ℝ (eqBasis n hn 0) (eqBasis n hn 1) = (0 : ℝ) := by
  rw [inner_eqBasis, eqBasis_apply, if_neg (eqIdx0_ne n hn (b := 0) (b' := 1) (by decide))]

theorem norm_neg_eqBasis (b : Fin 2) : ‖-eqBasis n hn b‖ = 1 := by
  rw [norm_neg, norm_eqBasis]

theorem inner_neg_eqBasis_zero_one :
    inner ℝ (-eqBasis n hn 0) (-eqBasis n hn 1) = (0 : ℝ) := by
  rw [inner_neg_neg, inner_eqBasis_zero_one]

theorem zero_eq_castSucc : (0 : Fin (n + 1)) = (⟨0, hn⟩ : Fin n).castSucc :=
  Fin.ext (by simp)

include hn in
theorem last_ne_zero_of_pos : (Fin.last n : Fin (n + 1)) ≠ 0 := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_last, Fin.val_zero] at hv
  omega

/-- The plane coordinate of the pair is the complex coordinate `0` of the equator embedding. -/
theorem equatorEmb_apply_zero (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    Gen.equatorEmb n a 0 = planeC (eqBasis n hn 0) (eqBasis n hn 1) a := by
  rw [zero_eq_castSucc n hn, Gen.equatorEmb_castSucc, planeC, inner_eqBasis, inner_eqBasis]
  rfl

theorem planeE_eqBasis_apply (w : ℂ) (j : Fin (2 * n + 1)) :
    planeE (eqBasis n hn 0) (eqBasis n hn 1) w j
      = (if j = eqIdx0 n hn 0 then w.re else 0) + (if j = eqIdx0 n hn 1 then w.im else 0) := by
  rw [planeE, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, eqBasis_apply, eqBasis_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- Off the two coordinates of the plane, a plane substitution changes nothing. -/
theorem planeSub_eqBasis_apply_of_ne (f : ℂ → ℂ) (a : EuclideanSpace ℝ (Fin (2 * n + 1)))
    {j : Fin (2 * n + 1)} (h0 : j ≠ eqIdx0 n hn 0) (h1 : j ≠ eqIdx0 n hn 1) :
    planeSub (eqBasis n hn 0) (eqBasis n hn 1) f a j = a j := by
  rw [planeSub, planeRest, PiLp.add_apply, PiLp.sub_apply, planeE_eqBasis_apply,
    planeE_eqBasis_apply]
  simp [h0, h1]

/-- **The equator embedding intertwines a plane substitution with the substitution in the
complex coordinate `0`.** -/
theorem equatorEmb_planeSub (f : ℂ → ℂ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    Gen.equatorEmb n (planeSub (eqBasis n hn 0) (eqBasis n hn 1) f a)
      = Function.update (Gen.equatorEmb n a) 0 (f (Gen.equatorEmb n a 0)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Function.update_of_ne (last_ne_zero_of_pos n hn), Gen.equatorEmb_last,
      Gen.equatorEmb_last, planeSub_eqBasis_apply_of_ne n hn f a
        (eqFwd_inr_ne_eqIdx0 n hn 0) (eqFwd_inr_ne_eqIdx0 n hn 1)]
  · intro i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      rw [← zero_eq_castSucc n hn, Function.update_self, equatorEmb_apply_zero n hn,
        equatorEmb_apply_zero n hn, planeC_planeSub (norm_eqBasis n hn 0)
          (norm_eqBasis n hn 1) (inner_eqBasis_zero_one n hn)]
    · have hne : (i.castSucc : Fin (n + 1)) ≠ 0 := by
        rw [zero_eq_castSucc n hn]
        exact fun he => hi (Fin.castSucc_injective n he)
      rw [Function.update_of_ne hne, Gen.equatorEmb_castSucc, Gen.equatorEmb_castSucc,
        planeSub_eqBasis_apply_of_ne n hn f a (eqFwd_ne_eqIdx0 n hn hi 0 0)
          (eqFwd_ne_eqIdx0 n hn hi 0 1),
        planeSub_eqBasis_apply_of_ne n hn f a (eqFwd_ne_eqIdx0 n hn hi 1 0)
          (eqFwd_ne_eqIdx0 n hn hi 1 1)]

/-- **The bridge to `KGen.psiVec`.**  The right-hand side is `KGen.psiVec n k (Gen.equatorEmb n
a)` by definition (`CharClass/LIXKGenMap.lean`), stated here without the `CharClass` import. -/
theorem equatorEmb_joinPow (k : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    Gen.equatorEmb n (joinPow (eqBasis n hn 0) (eqBasis n hn 1) k a)
      = Function.update (Gen.equatorEmb n a) 0 (joinC k (Gen.equatorEmb n a 0)) :=
  equatorEmb_planeSub n hn (joinC k) a

/-- **`ψ_k` at the equator is a radial map.** -/
theorem isRadialMap_joinPow_equator (k : ℕ) :
    IsRadialMap (joinPow (eqBasis n hn 0) (eqBasis n hn 1) k) :=
  isRadialMap_joinPow (norm_eqBasis n hn 0) (norm_eqBasis n hn 1)
    (inner_eqBasis_zero_one n hn) k

/-- The export's `ψ_k` for the ruled pair `e₁ := −ε₀`, `e₂ := −ε₁`. -/
theorem joinPowNeg_exportPair (k : ℕ) :
    joinPowNeg (-eqBasis n hn 0) (-eqBasis n hn 1) k
      = joinPow (eqBasis n hn 0) (eqBasis n hn 1) k :=
  joinPowNeg_neg_neg _ _ k

/-- **Step A's `hGe`, at the level of the map**: the export's `ψ_k` for the ruled pair is
`KGen.psiVec n k` through the equator embedding. -/
theorem equatorEmb_joinPowNeg_exportPair (k : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    Gen.equatorEmb n (joinPowNeg (-eqBasis n hn 0) (-eqBasis n hn 1) k a)
      = Function.update (Gen.equatorEmb n a) 0 (joinC k (Gen.equatorEmb n a 0)) := by
  rw [joinPowNeg_exportPair, equatorEmb_joinPow]

/-! ## The seam generator -/

/-- **The rank-`n` seam generator is a sphere unitary.** -/
theorem isSphereUnitary_genSphere : IsSphereUnitary (Gen.genSphere n) where
  continuousOn := Gen.continuousOn_genSphere n
  star_mul_self := fun _ hy => Gen.genSphere_conjTranspose_mul_self n hy
  mul_star_self := fun _ hy => Gen.genSphere_mul_conjTranspose n hy

/-- The generator read at `ψ_k y` is the block of the seam generator at `KGen.psiVec n k` of
the normalised point. -/
theorem genSphere_joinPow (k : ℕ) (y : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    Gen.genSphere n (joinPow (eqBasis n hn 0) (eqBasis n hn 1) k y)
      = Gen.genU2 n (Function.update (Gen.equatorEmb n ((‖y‖⁻¹ : ℝ) • y)) 0
          (joinC k (Gen.equatorEmb n ((‖y‖⁻¹ : ℝ) • y) 0))) := by
  have hΨ := isRadialMap_joinPow_equator n hn k
  rw [Gen.genSphere, hΨ.norm_map, ← hΨ.map_smul _ (inv_nonneg.mpr (norm_nonneg y)),
    equatorEmb_joinPow]

theorem genSphere_eqBasis (b : Fin 2) :
    Gen.genSphere n (eqBasis n hn b) = Gen.genU2 n (Gen.equatorEmb n (eqBasis n hn b)) := by
  rw [Gen.genSphere, norm_eqBasis, inv_one, one_smul]

/-- **The ball extension of the wall part, at the centre**: the seam block at the unit vector
`Gen.equatorEmb n ε₀`. -/
theorem ballWall_genSphere_zero :
    ballWall (-eqBasis n hn 0) (-eqBasis n hn 1) (Gen.genSphere n) 0
      = Gen.genU2 n (Gen.equatorEmb n (eqBasis n hn 0)) := by
  rw [ballWall_zero (norm_neg_eqBasis n hn 0) (norm_neg_eqBasis n hn 1)
    (inner_neg_eqBasis_zero_one n hn), neg_neg, genSphere_eqBasis]

/-- **THE RANK-`n` EXPORT.**  For the seam generator `Gen.genSphere n` and the ruled pair
`e₁ := −ε₀`, `e₂ := −ε₁`, the renormalised generator `ũ` satisfies `ũ^{k+1} ≃ ũ ∘ ψ_k` on the
unit sphere of `E n`, where `ψ_k = joinPow ε₀ ε₁ k` is `KGen.psiVec n k` through the equator
embedding (`equatorEmb_joinPow`), through maps continuous and unitary off the origin. -/
theorem exists_homotopy_pow_comp_genSphere (k : ℕ) :
    ∃ G : ℝ → EuclideanSpace ℝ (Fin (2 * n + 1)) → Matrix (Fin n) (Fin n) ℂ,
      ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * n + 1)) => G p.1 p.2)
        {p : ℝ × EuclideanSpace ℝ (Fin (2 * n + 1)) | p.2 ≠ 0} ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n + 1)),
        G 0 y = (normGen (-eqBasis n hn 0) (-eqBasis n hn 1) (Gen.genSphere n) y) ^ (k + 1)) ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n + 1)), ‖y‖ = 1 →
        G 1 y = normGen (-eqBasis n hn 0) (-eqBasis n hn 1) (Gen.genSphere n)
          (joinPow (eqBasis n hn 0) (eqBasis n hn 1) k y)) ∧
      (∀ (θ : ℝ) (y : EuclideanSpace ℝ (Fin (2 * n + 1))), y ≠ 0 →
        (G θ y)ᴴ * G θ y = 1) ∧
      (∀ (θ : ℝ) (y : EuclideanSpace ℝ (Fin (2 * n + 1))), y ≠ 0 →
        G θ y * (G θ y)ᴴ = 1) := by
  have h := exists_homotopy_pow_comp_normGen_sphere (norm_neg_eqBasis n hn 0)
    (norm_neg_eqBasis n hn 1) (inner_neg_eqBasis_zero_one n hn) (isSphereUnitary_genSphere n) k
  rwa [joinPowNeg_exportPair n hn k] at h

end Equator

end

end Powers
end LIX
end GroupApproximation
