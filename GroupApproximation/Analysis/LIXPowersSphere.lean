import GroupApproximation.Analysis.LIXPowersHomotopy

/-!
# The powers homotopy for a generator that is unitary only off the origin

`Analysis/LIXPowersHomotopy.lean` exports `u^{k+1} ≃ u ∘ ψ_k` for a **ball unitary** `u`:
continuous on all of `E` and unitary on the closed unit ball.  The generator the rank-`n`
tower actually has is `Gen.genSphere n y = Gen.genU2 n (Gen.equatorEmb n (‖y‖⁻¹ • y))`
(`Analysis/LIXGenericEquator.lean`), which is continuous and unitary at every `y ≠ 0` and
extends over **no** ball: its restriction to the sphere represents the nonzero element the
whole construction is about, so it is not null-homotopic.  This file states the export over
exactly what that generator supplies.

## The hypothesis

```lean
structure IsSphereUnitary (Ω : E → Matrix n n ℂ) : Prop where
  continuousOn  : ContinuousOn Ω {y : E | y ≠ 0}
  star_mul_self : ∀ y : E, y ≠ 0 → (Ω y)ᴴ * Ω y = 1
  mul_star_self : ∀ y : E, y ≠ 0 → Ω y * (Ω y)ᴴ = 1
```

It is enough because every map the powers chain precomposes with -- the angle
reparametrisations `angleFam`, the wall retraction `wallRetract`, the join power
`joinPowNeg` -- preserves the norm, so from a point `y ≠ 0` the construction never reaches
the origin.  The ball was never used by the homotopy; it is used by the *clutched* route
(the seam gauge reads the clutching function at the centre), which is off the critical path
(`notes/lix-stronger-lane-reports/sp-powers.md` §0.3) and keeps `IsBallUnitary`.

Nothing in the four ball files is edited: every statement here is new, and the one lemma
whose hypothesis was quantified over the closed ball, `pinchIdentification_angleRepar`, is
reused through `sphereCut`, which agrees with the generator on the unit sphere and is `1`
elsewhere.

## Main results

* `IsSphereUnitary` with `mul`, `star`, `pow`, `compRadial`.
* `continuousOn_reparProd`, `unit_reparProd_sphere` -- the ordered product off the origin.
* `pinchIdentification_angleRepar_sphere` -- the pinch identification from the wall
  condition on the unit sphere only.
* `isSphereUnitary_normGen`, `normGen_wall_sphere`, `wallPart_mul_normGen_sphere`.
* `exists_homotopy_pow_comp_sphere`, and **the export**
  `exists_homotopy_pow_comp_normGen_sphere`: for any sphere unitary `U`, an explicit `G`,
  continuous on `ℝ × (E ∖ 0)`, with `G 0 = ũ^{k+1}`, `G 1 = ũ ∘ ψ_k` on the unit sphere, and
  unitary at every `(θ, y)` with `y ≠ 0`, where `ũ = normGen e₁ e₂ U`.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Sphere unitaries -/

section SphereUnitary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- A **sphere unitary**: a matrix field on `E` which is continuous and unitary at every
point off the origin.  The rank-`n` seam generator `Gen.genSphere n` is one; it is not a ball
unitary and cannot be made one. -/
structure IsSphereUnitary (Ω : E → Matrix n n ℂ) : Prop where
  continuousOn : ContinuousOn Ω {y : E | y ≠ 0}
  star_mul_self : ∀ y : E, y ≠ 0 → (Ω y)ᴴ * Ω y = 1
  mul_star_self : ∀ y : E, y ≠ 0 → Ω y * (Ω y)ᴴ = 1

theorem IsSphereUnitary.unit {Ω : E → Matrix n n ℂ} (hΩ : IsSphereUnitary Ω) {y : E}
    (hy : y ≠ 0) : (Ω y)ᴴ * Ω y = 1 ∧ Ω y * (Ω y)ᴴ = 1 :=
  ⟨hΩ.star_mul_self y hy, hΩ.mul_star_self y hy⟩

/-- A unit vector is not the origin. -/
theorem sphere_ne_zero {y : E} (hy : ‖y‖ = 1) : y ≠ 0 := by
  intro h
  rw [h, norm_zero] at hy
  exact zero_ne_one hy

/-- A radial map sends nonzero points to nonzero points. -/
theorem IsRadialMap.ne_zero {Ψ : E → E} (hΨ : IsRadialMap Ψ) {y : E} (hy : y ≠ 0) :
    Ψ y ≠ 0 := by
  rw [← norm_ne_zero_iff, hΨ.norm_map]
  exact norm_ne_zero_iff.mpr hy

/-- The pointwise product of two sphere unitaries is a sphere unitary. -/
theorem IsSphereUnitary.mul {B Ω : E → Matrix n n ℂ} (hB : IsSphereUnitary B)
    (hΩ : IsSphereUnitary Ω) : IsSphereUnitary fun y => B y * Ω y where
  continuousOn := hB.continuousOn.mul hΩ.continuousOn
  star_mul_self := fun _ hy => (unit_mul (hB.unit hy) (hΩ.unit hy)).1
  mul_star_self := fun _ hy => (unit_mul (hB.unit hy) (hΩ.unit hy)).2

/-- The pointwise adjoint of a sphere unitary is a sphere unitary. -/
theorem IsSphereUnitary.star {Ω : E → Matrix n n ℂ} (hΩ : IsSphereUnitary Ω) :
    IsSphereUnitary fun y => (Ω y)ᴴ where
  continuousOn := by
    have h : Continuous fun A : Matrix n n ℂ => Aᴴ := continuous_id.matrix_conjTranspose
    exact h.comp_continuousOn hΩ.continuousOn
  star_mul_self := fun _ hy => (unit_star (hΩ.unit hy)).1
  mul_star_self := fun _ hy => (unit_star (hΩ.unit hy)).2

/-- A sphere unitary precomposed with a radial map is a sphere unitary. -/
theorem IsSphereUnitary.compRadial {Ω : E → Matrix n n ℂ} {Ψ : E → E}
    (hΩ : IsSphereUnitary Ω) (hΨ : IsRadialMap Ψ) : IsSphereUnitary fun y => Ω (Ψ y) where
  continuousOn := by
    refine hΩ.continuousOn.comp hΨ.continuous.continuousOn ?_
    intro y hy
    exact hΨ.ne_zero hy
  star_mul_self := fun _ hy => hΩ.star_mul_self _ (hΨ.ne_zero hy)
  mul_star_self := fun _ hy => hΩ.mul_star_self _ (hΨ.ne_zero hy)

/-- A pointwise power of a sphere unitary is a sphere unitary. -/
theorem IsSphereUnitary.pow {Ω : E → Matrix n n ℂ} (hΩ : IsSphereUnitary Ω) (k : ℕ) :
    IsSphereUnitary fun y => (Ω y) ^ k := by
  induction k with
  | zero =>
      refine ⟨?_, fun _ _ => ?_, fun _ _ => ?_⟩
      · simp only [pow_zero]
        exact continuousOn_const
      · simp
      · simp
  | succ j ih =>
      have h := ih.mul hΩ
      simpa only [pow_succ] using h

end SphereUnitary

/-! ## The ordered product off the origin -/

section Repar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]
  {W : E → Matrix n n ℂ} {P : ℕ → ℝ → E → E}

/-- **Joint continuity of the ordered product off the origin**, for a family that never
sends a nonzero point to the origin. -/
theorem continuousOn_reparProd (hW : ContinuousOn W {y : E | y ≠ 0})
    (hPc : ∀ j : ℕ, Continuous fun p : ℝ × E => P j p.1 p.2)
    (hPn : ∀ (j : ℕ) (θ : ℝ) (y : E), y ≠ 0 → P j θ y ≠ 0) (k : ℕ) :
    ContinuousOn (fun p : ℝ × E => reparProd W P p.1 p.2 k) {p : ℝ × E | p.2 ≠ 0} := by
  induction k with
  | zero =>
      simp only [reparProd_zero]
      exact continuousOn_const
  | succ j ih =>
      simp only [reparProd_succ]
      refine ih.mul (hW.comp (hPc j).continuousOn ?_)
      intro p hp
      exact hPn j p.1 p.2 hp

/-- **Unitarity of the ordered product off the origin.** -/
theorem unit_reparProd_sphere (hW : IsSphereUnitary W)
    (hPn : ∀ (j : ℕ) (θ : ℝ) (y : E), y ≠ 0 → P j θ y ≠ 0) (θ : ℝ) {y : E} (hy : y ≠ 0)
    (k : ℕ) :
    (reparProd W P θ y k)ᴴ * reparProd W P θ y k = 1 ∧
      reparProd W P θ y k * (reparProd W P θ y k)ᴴ = 1 := by
  induction k with
  | zero =>
      rw [reparProd_zero]
      simp
  | succ j ih =>
      rw [reparProd_succ]
      exact unit_mul ih (hW.unit (hPn j θ y hy))

/-- The ordered product only reads the clutching function at the points the family visits. -/
theorem reparProd_congr_left {W' : E → Matrix n n ℂ} {θ : ℝ} {y : E}
    (h : ∀ j : ℕ, W (P j θ y) = W' (P j θ y)) (k : ℕ) :
    reparProd W P θ y k = reparProd W' P θ y k := by
  induction k with
  | zero => rw [reparProd_zero, reparProd_zero]
  | succ j ih => rw [reparProd_succ, reparProd_succ, ih, h j]

end Repar

/-! ## The pinch identification from the unit sphere -/

section Pinch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}
  {n : Type*} [Fintype n] [DecidableEq n] {W : E → Matrix n n ℂ}

/-- `W` on the unit sphere and the identity matrix elsewhere.  It is a device for reusing a
lemma whose hypothesis is quantified over the closed ball: the ordered product at a unit
vector reads its clutching function only at unit vectors. -/
def sphereCut (W : E → Matrix n n ℂ) (y : E) : Matrix n n ℂ :=
  if ‖y‖ = 1 then W y else 1

theorem sphereCut_of_norm_eq_one {y : E} (hy : ‖y‖ = 1) : sphereCut W y = W y := by
  rw [sphereCut, if_pos hy]

theorem sphereCut_of_norm_ne_one {y : E} (hy : ‖y‖ ≠ 1) : sphereCut W y = 1 := by
  rw [sphereCut, if_neg hy]

/-- **The pinch identification for the join power, from the wall condition on the unit
sphere only.** -/
theorem pinchIdentification_angleRepar_sphere (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (k : ℕ)
    (hwall : ∀ y : E, ‖y‖ = 1 → W (wallRetract e₁ e₂ y) = 1) :
    PinchIdentification W (angleFam e₁ e₂ k) (joinPowNeg e₁ e₂ k) (k + 1) := by
  have hwall' : ∀ y : E, ‖y‖ ≤ 1 → sphereCut W (wallRetract e₁ e₂ y) = 1 := by
    intro y _
    by_cases hw : ‖wallRetract e₁ e₂ y‖ = 1
    · rw [sphereCut_of_norm_eq_one hw]
      refine hwall y ?_
      rwa [(isRadialMap_wallRetract h₁ h₂ h₁₂).norm_map] at hw
    · exact sphereCut_of_norm_ne_one hw
  have hp := pinchIdentification_angleRepar h₁ h₂ h₁₂ k hwall'
  intro y hy
  have hleft : reparProd W (angleFam e₁ e₂ k) 1 y (k + 1)
      = reparProd (sphereCut W) (angleFam e₁ e₂ k) 1 y (k + 1) := by
    refine reparProd_congr_left (fun j => ?_) (k + 1)
    have hj : ‖angleFam e₁ e₂ k j 1 y‖ = 1 := by
      rw [norm_angleFam h₁ h₂ h₁₂, hy]
    exact (sphereCut_of_norm_eq_one (W := W) hj).symm
  have hΨ : ‖joinPowNeg e₁ e₂ k y‖ = 1 := by
    rw [(isRadialMap_joinPowNeg h₁ h₂ h₁₂ k).norm_map, hy]
  rw [hleft, hp y hy, sphereCut_of_norm_eq_one hΨ]

end Pinch

/-! ## The renormalised generator off the origin -/

section Normalise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}
  {n : Type*} [Fintype n] [DecidableEq n] {U : E → Matrix n n ℂ}

theorem isSphereUnitary_wallPart (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsSphereUnitary U) :
    IsSphereUnitary (wallPart e₁ e₂ U) :=
  hU.compRadial (isRadialMap_wallRetract h₁ h₂ h₁₂)

theorem isSphereUnitary_normGen (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsSphereUnitary U) :
    IsSphereUnitary (normGen e₁ e₂ U) :=
  (isSphereUnitary_wallPart h₁ h₂ h₁₂ hU).star.mul hU

/-- **The renormalised generator is the identity on the wall**, off the origin. -/
theorem normGen_wall_sphere (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsSphereUnitary U) {y : E} (hy : y ≠ 0) :
    normGen e₁ e₂ U (wallRetract e₁ e₂ y) = 1 := by
  rw [normGen, wallRetract_idem h₁ h₂ h₁₂]
  exact hU.star_mul_self _ ((isRadialMap_wallRetract h₁ h₂ h₁₂).ne_zero hy)

/-- The factorisation `u = (u on the wall) · ũ`, off the origin. -/
theorem wallPart_mul_normGen_sphere (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsSphereUnitary U) {y : E} (hy : y ≠ 0) :
    wallPart e₁ e₂ U y * normGen e₁ e₂ U y = U y := by
  rw [wallPart, normGen, ← Matrix.mul_assoc,
    hU.mul_star_self _ ((isRadialMap_wallRetract h₁ h₂ h₁₂).ne_zero hy), Matrix.one_mul]

end Normalise

/-! ## The wall part extended over the ball

The generator is not a ball unitary, but its **wall part** `y ↦ U (wallRetract y)` extends
to one: on the unit sphere the wall retraction lands in the wall, a disc, and sliding the
point towards the wall point `−e₁` as the radius shrinks never passes through the origin.
Lane lix-tower consumes this twice: it gauges the north frame over the whole cap, so the
seam becomes `ũ = Aᴴ u`, and it contracts `diag(Aᴴ, 1)` to the constant `diag(B(0)ᴴ, 1)`
with no appeal to path-connectedness of `U(n)`. -/

section BallWall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}
  {n : Type*} [Fintype n] [DecidableEq n] {U : E → Matrix n n ℂ}

/-- **The shifted wall point never vanishes.**  If `wallRetract y + (1 − ‖y‖)(−e₁) = 0` then
`wallRetract y = (1 − ‖y‖) e₁`; its `e₁`-coordinate is `−|z| ≤ 0`, so `‖y‖ ≥ 1`, and its norm
is `‖y‖`, so `‖y‖ = ‖y‖ − 1`. -/
theorem wallShift_ne_zero (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (y : E) :
    wallRetract e₁ e₂ y + (1 - ‖y‖) • (-e₁) ≠ 0 := by
  intro hv
  have ha : wallRetract e₁ e₂ y = (1 - ‖y‖) • e₁ := by
    rw [smul_neg, add_neg_eq_zero] at hv
    exact hv
  have hre : inner ℝ e₁ (wallRetract e₁ e₂ y) = -‖planeC e₁ e₂ y‖ := by
    rw [← planeC_re e₁ e₂, wallRetract, planeC_planeSub h₁ h₂ h₁₂, wallC]
    simp
  have h11 : inner ℝ e₁ e₁ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h₁, one_pow]
  have hc : inner ℝ e₁ (wallRetract e₁ e₂ y) = 1 - ‖y‖ := by
    rw [ha, real_inner_smul_right, h11, mul_one]
  have hnorm : ‖y‖ = |1 - ‖y‖| := by
    have h := (isRadialMap_wallRetract h₁ h₂ h₁₂).norm_map y
    rw [ha, norm_smul, h₁, mul_one, Real.norm_eq_abs] at h
    exact h.symm
  have hle : 1 - ‖y‖ ≤ 0 := by
    rw [← hc, hre]
    exact neg_nonpos.mpr (norm_nonneg _)
  rw [abs_of_nonpos hle] at hnorm
  linarith

theorem continuous_wallShift (e₁ e₂ : E) :
    Continuous fun y : E => wallRetract e₁ e₂ y + (1 - ‖y‖) • (-e₁) :=
  (continuous_planeSub e₁ e₂ continuous_wallC).add
    ((continuous_const.sub continuous_norm).smul continuous_const)

/-- **The wall part over the ball**: `y ↦ U (wallRetract y + (1 − ‖y‖)(−e₁))`. -/
def ballWall (e₁ e₂ : E) (U : E → Matrix n n ℂ) (y : E) : Matrix n n ℂ :=
  U (wallRetract e₁ e₂ y + (1 - ‖y‖) • (-e₁))

/-- **The wall part of a sphere unitary extends to a ball unitary**; it is in fact continuous
and unitary on all of `E`. -/
theorem isBallUnitary_ballWall (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsSphereUnitary U) :
    IsBallUnitary (ballWall e₁ e₂ U) where
  continuous := hU.continuousOn.comp_continuous (continuous_wallShift e₁ e₂)
    (fun y => wallShift_ne_zero h₁ h₂ h₁₂ y)
  star_mul_self := fun y _ => hU.star_mul_self _ (wallShift_ne_zero h₁ h₂ h₁₂ y)
  mul_star_self := fun y _ => hU.mul_star_self _ (wallShift_ne_zero h₁ h₂ h₁₂ y)

/-- On the unit sphere the extension is the wall part. -/
theorem ballWall_of_norm_eq_one {y : E} (hy : ‖y‖ = 1) :
    ballWall e₁ e₂ U y = wallPart e₁ e₂ U y := by
  rw [ballWall, wallPart, hy, sub_self, zero_smul, add_zero]

/-- At the centre the extension is the generator at the wall point `−e₁`. -/
theorem ballWall_zero (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) :
    ballWall e₁ e₂ U 0 = U (-e₁) := by
  rw [ballWall, (isRadialMap_wallRetract h₁ h₂ h₁₂).map_zero, norm_zero, sub_zero, one_smul,
    zero_add]

/-- The renormalised generator on the unit sphere, through the ball extension. -/
theorem normGen_eq_ballWall_mul {y : E} (hy : ‖y‖ = 1) :
    normGen e₁ e₂ U y = (ballWall e₁ e₂ U y)ᴴ * U y := by
  rw [ballWall_of_norm_eq_one hy] <;> rfl

end BallWall

/-! ## The export -/

section Homotopy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}
  {n : Type*} [Fintype n] [DecidableEq n] {U : E → Matrix n n ℂ}

/-- **The bare Eckmann--Hilton homotopy off the origin.**  For a sphere unitary that is the
identity on the wall of the unit sphere, `U^{k+1}` and `U ∘ ψ_k` are homotopic through maps
that are unitary at every nonzero point, by the ordered product of the `k + 1` angle
reparametrisations. -/
theorem exists_homotopy_pow_comp_sphere (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsSphereUnitary U)
    (hwall : ∀ y : E, ‖y‖ = 1 → U (wallRetract e₁ e₂ y) = 1) (k : ℕ) :
    ∃ G : ℝ → E → Matrix n n ℂ,
      ContinuousOn (fun p : ℝ × E => G p.1 p.2) {p : ℝ × E | p.2 ≠ 0} ∧
      (∀ y : E, G 0 y = (U y) ^ (k + 1)) ∧
      (∀ y : E, ‖y‖ = 1 → G 1 y = U (joinPowNeg e₁ e₂ k y)) ∧
      (∀ (θ : ℝ) (y : E), y ≠ 0 → (G θ y)ᴴ * G θ y = 1) ∧
      (∀ (θ : ℝ) (y : E), y ≠ 0 → G θ y * (G θ y)ᴴ = 1) := by
  have hPn : ∀ (j : ℕ) (θ : ℝ) (y : E), y ≠ 0 → angleFam e₁ e₂ k j θ y ≠ 0 := by
    intro j θ y hy
    rw [← norm_ne_zero_iff, norm_angleFam h₁ h₂ h₁₂]
    exact norm_ne_zero_iff.mpr hy
  refine ⟨fun θ y => reparProd U (angleFam e₁ e₂ k) θ y (k + 1),
    continuousOn_reparProd hU.continuousOn (continuous_angleFam e₁ e₂ k) hPn (k + 1),
    fun y => reparProd_param_zero (angleFam_param_zero e₁ e₂ k) U y (k + 1),
    fun y hy => pinchIdentification_angleRepar_sphere h₁ h₂ h₁₂ k hwall y hy,
    fun θ y hy => (unit_reparProd_sphere hU hPn θ hy (k + 1)).1,
    fun θ y hy => (unit_reparProd_sphere hU hPn θ hy (k + 1)).2⟩

/-- **THE EXPORT for the rank-`n` tower.**  For any sphere unitary `U` -- in particular the
seam generator `Gen.genSphere n` -- the renormalised generator `ũ = normGen e₁ e₂ U` satisfies
`ũ^{k+1} ≃ ũ ∘ ψ_k` on the unit sphere, through maps continuous and unitary off the origin.
No hypothesis on the generator beyond `IsSphereUnitary`. -/
theorem exists_homotopy_pow_comp_normGen_sphere (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsSphereUnitary U) (k : ℕ) :
    ∃ G : ℝ → E → Matrix n n ℂ,
      ContinuousOn (fun p : ℝ × E => G p.1 p.2) {p : ℝ × E | p.2 ≠ 0} ∧
      (∀ y : E, G 0 y = (normGen e₁ e₂ U y) ^ (k + 1)) ∧
      (∀ y : E, ‖y‖ = 1 → G 1 y = normGen e₁ e₂ U (joinPowNeg e₁ e₂ k y)) ∧
      (∀ (θ : ℝ) (y : E), y ≠ 0 → (G θ y)ᴴ * G θ y = 1) ∧
      (∀ (θ : ℝ) (y : E), y ≠ 0 → G θ y * (G θ y)ᴴ = 1) :=
  exists_homotopy_pow_comp_sphere h₁ h₂ h₁₂ (isSphereUnitary_normGen h₁ h₂ h₁₂ hU)
    (fun _ hy => normGen_wall_sphere h₁ h₂ h₁₂ hU (sphere_ne_zero hy)) k

end Homotopy

end

end Powers
end LIX
end GroupApproximation
