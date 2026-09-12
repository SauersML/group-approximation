import GroupApproximation.Analysis.LIXPowersPinch

/-!
# The renormalised seam generator

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3, deliverable 2 of the powers lane.
`Analysis/LIXPowersPinch.lean` discharges the pinch identification for any clutching
function that is the identity matrix on the wall.  The seam generator is not, so it has to
be renormalised, and this file does that -- **with no contraction and no appeal to the
topology of `U(n)`.**

## Why nothing has to be contracted

The gauge lemma of `Analysis/LIXPowersGauge.lean` asks only for a *ball* unitary:
continuous and unitary on the closed unit ball, with no condition at the centre.  That is
weaker than "null-homotopic", and it is exactly what the wall retraction supplies for free.

`wallRetract e₁ e₂ (z, v) = (−|z|, v)` is norm-preserving and positively homogeneous,
hence an `IsRadialMap`, hence `U ∘ wallRetract` is a ball unitary whenever `U` is.  Setting

```text
ũ = (U ∘ wallRetract)ᴴ · U
```

gives a ball unitary with `ũ ≡ 1` on the wall (because `wallRetract` is idempotent), and
every comparison the chain needs is then a *gauge* step rather than a homotopy:

* `clutch u ≅ clutch ũ`, gauge factor `U ∘ wallRetract`;
* `clutch (u ∘ ψ) ≅ clutch (ũ ∘ ψ)`, gauge factor `(U ∘ wallRetract) ∘ ψ`, again a ball
  unitary because `ψ` is radial;
* `clutch (u^m) ≅ clutch (ũ^m)`, gauge factor `u^m · (ũ^m)ᴴ`, a product of ball unitaries.

The last one is the one that looked as if it needed a homotopy `θ ↦ (A_θ ũ)^m ũ^{-m}`, and
would have, had the gauge lemma been stated for disc unitaries.  It is not, so it does not.
The mathematical content is only that `U ∘ wallRetract` factors through the wall, which is
a disc, so it extends over the ball by the very same formula; nothing about `π₀(U(n))`
enters, and the program does not owe path-connectedness of the unitary group.

## Main results

* `wallRetract_idem`, and the plane-coordinate lemmas it needs.
* `normGen`, `isBallUnitary_normGen`, `normGen_wall` -- the renormalisation and its
  defining property, which is precisely the hypothesis `pinchIdentification_angleRepar`
  takes.
* `clutchEquiv_normGen`, `clutchEquiv_normGen_pow`, `clutchEquiv_normGen_comp` -- the three
  gauge transports.
* `ClutchEquiv` with `refl`/`symm`/`trans`, the relation the chain is assembled in.  It is
  the same shape as `CharClass.ContinuousMvNEquiv`, which is what `sp-oddside` consumes;
  the bridge between them is one `Iff.rfl` and belongs with that lane's file, not here.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Murray--von Neumann equivalence of continuous projection fields -/

section Equiv

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Murray--von Neumann equivalence of continuous fields**, in the shape the clutching
layer produces.  This is definitionally `CharClass.ContinuousMvNEquiv`; it is restated here
so that the `Analysis/` files do not have to import `CharClass`. -/
def ClutchEquiv (P Q : X → Matrix ι ι ℂ) : Prop :=
  ∃ V : X → Matrix ι ι ℂ, Continuous V ∧ (∀ x, (V x)ᴴ * V x = P x) ∧
    (∀ x, V x * (V x)ᴴ = Q x)

theorem ClutchEquiv.symm {P Q : X → Matrix ι ι ℂ} (h : ClutchEquiv P Q) :
    ClutchEquiv Q P := by
  obtain ⟨V, hVc, h1, h2⟩ := h
  refine ⟨fun x => (V x)ᴴ, hVc.matrix_conjTranspose, fun x => ?_, fun x => ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]
    exact h2 x
  · rw [Matrix.conjTranspose_conjTranspose]
    exact h1 x

/-- Transitivity.  The two outer projections have to be idempotent, which they always are
here: they are `clutchMat` of a clutching datum. -/
theorem ClutchEquiv.trans {P Q R : X → Matrix ι ι ℂ} (hP : ∀ x, P x * P x = P x)
    (hR : ∀ x, R x * R x = R x) (h₁ : ClutchEquiv P Q) (h₂ : ClutchEquiv Q R) :
    ClutchEquiv P R := by
  obtain ⟨V, hVc, hV1, hV2⟩ := h₁
  obtain ⟨W, hWc, hW1, hW2⟩ := h₂
  refine ⟨fun x => W x * V x, hWc.matrix_mul hVc, fun x => ?_, fun x => ?_⟩
  · calc (W x * V x)ᴴ * (W x * V x)
        = (V x)ᴴ * ((W x)ᴴ * W x) * V x := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (V x)ᴴ * (V x * (V x)ᴴ) * V x := by rw [hW1 x, hV2 x]
      _ = P x * P x := by
          rw [← hV1 x]
          simp only [Matrix.mul_assoc]
      _ = P x := hP x
  · calc (W x * V x) * (W x * V x)ᴴ
        = W x * (V x * (V x)ᴴ) * (W x)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = W x * ((W x)ᴴ * W x) * (W x)ᴴ := by rw [hV2 x, hW1 x]
      _ = R x * R x := by
          rw [← hW2 x]
          simp only [Matrix.mul_assoc]
      _ = R x := hR x

end Equiv

/-! ## The plane coordinates of a substitution -/

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}

theorem planeC_add (e₁ e₂ : E) (y w : E) :
    planeC e₁ e₂ (y + w) = planeC e₁ e₂ y + planeC e₁ e₂ w := by
  rw [planeC, planeC, planeC, inner_add_right, inner_add_right]
  push_cast
  ring

/-- The plane coordinate of a point of the plane is its own coordinate. -/
theorem planeC_planeE (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (w : ℂ) : planeC e₁ e₂ (planeE e₁ e₂ w) = w := by
  have h11 : inner ℝ e₁ e₁ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h₁, one_pow]
  have h22 : inner ℝ e₂ e₂ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h₂, one_pow]
  have h21 : inner ℝ e₂ e₁ = (0 : ℝ) := by rw [real_inner_comm]; exact h₁₂
  have hre : inner ℝ e₁ (planeE e₁ e₂ w) = w.re := by
    rw [planeE, inner_add_right, real_inner_smul_right, real_inner_smul_right, h11, h₁₂]
    ring
  have him : inner ℝ e₂ (planeE e₁ e₂ w) = w.im := by
    rw [planeE, inner_add_right, real_inner_smul_right, real_inner_smul_right, h21, h22]
    ring
  rw [planeC, hre, him]
  exact Complex.re_add_im w

/-- The plane coordinate of the orthogonal part vanishes. -/
theorem planeC_planeRest (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (y : E) : planeC e₁ e₂ (planeRest e₁ e₂ y) = 0 := by
  rw [planeC, inner_e₁_planeRest h₁ h₁₂, inner_e₂_planeRest h₂ h₁₂]
  simp

theorem planeC_planeSub (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (f : ℂ → ℂ) (y : E) :
    planeC e₁ e₂ (planeSub e₁ e₂ f y) = f (planeC e₁ e₂ y) := by
  rw [planeSub, planeC_add, planeC_planeRest h₁ h₂ h₁₂, planeC_planeE h₁ h₂ h₁₂, zero_add]

theorem planeRest_planeSub (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (f : ℂ → ℂ) (y : E) :
    planeRest e₁ e₂ (planeSub e₁ e₂ f y) = planeRest e₁ e₂ y := by
  rw [show planeRest e₁ e₂ (planeSub e₁ e₂ f y)
      = planeSub e₁ e₂ f y - planeE e₁ e₂ (planeC e₁ e₂ (planeSub e₁ e₂ f y)) from rfl,
    planeC_planeSub h₁ h₂ h₁₂]
  simp only [planeSub, planeRest]
  abel

/-- **Substitutions compose.** -/
theorem planeSub_comp (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (f g : ℂ → ℂ) (y : E) :
    planeSub e₁ e₂ g (planeSub e₁ e₂ f y) = planeSub e₁ e₂ (fun z => g (f z)) y := by
  rw [show planeSub e₁ e₂ g (planeSub e₁ e₂ f y)
      = planeRest e₁ e₂ (planeSub e₁ e₂ f y)
        + planeE e₁ e₂ (g (planeC e₁ e₂ (planeSub e₁ e₂ f y))) from rfl,
    planeRest_planeSub h₁ h₂ h₁₂, planeC_planeSub h₁ h₂ h₁₂, planeSub]

theorem wallC_idem (z : ℂ) : wallC (wallC z) = wallC z := by
  rw [wallC, wallC, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z)]

/-- **The wall retraction is idempotent**, which is what makes the renormalised generator
equal to `1` on the wall. -/
theorem wallRetract_idem (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (y : E) : wallRetract e₁ e₂ (wallRetract e₁ e₂ y) = wallRetract e₁ e₂ y := by
  rw [wallRetract, planeSub_comp h₁ h₂ h₁₂]
  congr 1
  funext z
  exact wallC_idem z

end Plane

/-! ## The renormalisation -/

section Normalise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}
  {n : Type*} [Fintype n] [DecidableEq n] {U : E → Matrix n n ℂ}

/-- The value of a clutching function on the wall, pulled back to `E`. -/
def wallPart (e₁ e₂ : E) (U : E → Matrix n n ℂ) : E → Matrix n n ℂ :=
  fun y => U (wallRetract e₁ e₂ y)

/-- **The renormalised generator.** -/
def normGen (e₁ e₂ : E) (U : E → Matrix n n ℂ) : E → Matrix n n ℂ :=
  fun y => (U (wallRetract e₁ e₂ y))ᴴ * U y

theorem isBallUnitary_wallPart (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) :
    IsBallUnitary (wallPart e₁ e₂ U) :=
  hU.compRadial (isRadialMap_wallRetract h₁ h₂ h₁₂)

theorem isBallUnitary_normGen (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) :
    IsBallUnitary (normGen e₁ e₂ U) :=
  (isBallUnitary_wallPart h₁ h₂ h₁₂ hU).star.mul hU

/-- **The renormalised generator is the identity on the wall.**  This is exactly the
hypothesis `pinchIdentification_angleRepar` consumes. -/
theorem normGen_wall (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (hU : IsBallUnitary U) {y : E} (hy : ‖y‖ ≤ 1) :
    normGen e₁ e₂ U (wallRetract e₁ e₂ y) = 1 := by
  have hnorm : ‖wallRetract e₁ e₂ y‖ ≤ 1 :=
    (isRadialMap_wallRetract h₁ h₂ h₁₂).mapsTo_ball hy
  rw [normGen, wallRetract_idem h₁ h₂ h₁₂]
  exact hU.star_mul_self _ hnorm

/-- The factorisation `u = (u on the wall) · ũ`. -/
theorem wallPart_mul_normGen (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) {y : E} (hy : ‖y‖ ≤ 1) :
    wallPart e₁ e₂ U y * normGen e₁ e₂ U y = U y := by
  have hnorm : ‖wallRetract e₁ e₂ y‖ ≤ 1 :=
    (isRadialMap_wallRetract h₁ h₂ h₁₂).mapsTo_ball hy
  rw [wallPart, normGen, ← Matrix.mul_assoc, hU.mul_star_self _ hnorm, Matrix.one_mul]

end Normalise

/-! ## The three gauge transports -/

section Transport

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {e₁ e₂ : E} {n : Type*} [Fintype n] [DecidableEq n]
  {t : X → ℝ} {ν : X → E} {U : E → Matrix n n ℂ} {Ψ : E → E}

/-- **Transport 1**: the generator and its renormalisation clutch equivalent
projections. -/
theorem clutchEquiv_normGen (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) :
    ClutchEquiv (fun x => clutchMat (t x) (coneMat U (ν x)))
      (fun x => clutchMat (t x) (coneMat (normGen e₁ e₂ U) (ν x))) := by
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_of_gauge_left (B := normGen e₁ e₂ U)
      (Ω := wallPart e₁ e₂ U) hc (isBallUnitary_normGen h₁ h₂ h₁₂ hU)
      (isBallUnitary_wallPart h₁ h₂ h₁₂ hU)
  refine ⟨V, hVc, fun x => ?_, hV2⟩
  rw [hV1 x]
  congr 1
  refine coneMat_congr (fun y hy => ?_) (ν x)
  exact wallPart_mul_normGen h₁ h₂ h₁₂ hU (le_of_eq hy)

/-- **Transport 2**: the `m`-th powers clutch equivalent projections.  The gauge factor is
`u^m · (ũ^m)ᴴ`, a product of ball unitaries; no homotopy is constructed. -/
theorem clutchEquiv_normGen_pow (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (m : ℕ) :
    ClutchEquiv (fun x => clutchMat (t x) (coneMat (fun y => (U y) ^ m) (ν x)))
      (fun x => clutchMat (t x) (coneMat (fun y => (normGen e₁ e₂ U y) ^ m) (ν x))) := by
  have hnorm := isBallUnitary_normGen h₁ h₂ h₁₂ hU
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_of_gauge_left (B := fun y => (normGen e₁ e₂ U y) ^ m)
      (Ω := fun y => (U y) ^ m * ((normGen e₁ e₂ U y) ^ m)ᴴ) hc (hnorm.pow m)
      ((hU.pow m).mul (hnorm.pow m).star)
  refine ⟨V, hVc, fun x => ?_, hV2⟩
  rw [hV1 x]
  congr 1
  refine coneMat_congr (fun y hy => ?_) (ν x)
  show (U y) ^ m * ((normGen e₁ e₂ U y) ^ m)ᴴ * (normGen e₁ e₂ U y) ^ m = (U y) ^ m
  rw [Matrix.mul_assoc, (hnorm.pow m).star_mul_self y (le_of_eq hy), Matrix.mul_one]

/-- **Transport 3**: the composites with a radial `ψ` clutch equivalent projections. -/
theorem clutchEquiv_normGen_comp (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U)
    (hΨ : IsRadialMap Ψ) :
    ClutchEquiv (fun x => clutchMat (t x) (coneMat (fun y => U (Ψ y)) (ν x)))
      (fun x => clutchMat (t x) (coneMat (fun y => normGen e₁ e₂ U (Ψ y)) (ν x))) := by
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_of_gauge_left (B := fun y => normGen e₁ e₂ U (Ψ y))
      (Ω := fun y => wallPart e₁ e₂ U (Ψ y)) hc
      ((isBallUnitary_normGen h₁ h₂ h₁₂ hU).compRadial hΨ)
      ((isBallUnitary_wallPart h₁ h₂ h₁₂ hU).compRadial hΨ)
  refine ⟨V, hVc, fun x => ?_, hV2⟩
  rw [hV1 x]
  congr 1
  refine coneMat_congr (fun y hy => ?_) (ν x)
  exact wallPart_mul_normGen h₁ h₂ h₁₂ hU (hΨ.mapsTo_ball (le_of_eq hy))

end Transport

end

end Powers
end LIX
end GroupApproximation
