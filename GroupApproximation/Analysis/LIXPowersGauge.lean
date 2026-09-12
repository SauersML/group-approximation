import GroupApproximation.Analysis.LIXClutching

/-!
# The gauge lemma for the clutching layer

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3 item 2.  `Analysis/LIXClutching.lean`
proves that a clutching function which extends over the closed unit ball produces a
projection equivalent to the *untwisted* one.  The stronger theorem needs the relative
form of the same statement: changing a clutching function `b` by a factor that extends
over the ball does not change the clutched projection up to Murray--von Neumann
equivalence of continuous fields.  That is the **gauge lemma**, and it is what turns a
homotopy `u^k ≃ u ∘ ψ_k` into an equality of clutched projections.

## The three results

* `exists_partialIsometry_of_gauge_right` -- **the gauge lemma.**  If `Ω` is unitary on
  the closed unit ball of `E` and continuous there, and `B` likewise, then
  `clutch (B·Ω)` and `clutch B` are Murray--von Neumann equivalent through an explicit
  continuous partial isometry.
* `isDiscUnitary_discOfHomotopy` -- **the disc form of a null-homotopy.**  A homotopy on
  the sphere from the constant `1` to `w`, read off the radius with a *plateau* on the
  inner half-ball, is a disc unitary restricting to `w`.  The plateau is what makes
  continuity at the centre free: on `‖y‖ ≤ 1/2` the disc unitary is literally the
  constant `1`, so no uniformity in the direction `y/‖y‖` is ever needed, and `E` need
  not be finite-dimensional.
* `exists_partialIsometry_of_homotopy` -- **homotopy invariance of clutching**, the
  combination of the two.  This is the tool the powers lane exports: homotopic clutching
  functions clutch equivalent projections, with no functional calculus, no local
  triviality and no compactness.

## Why the gauge factor goes on the right

`LIXClutching`'s seam isometry `seamMat t f g κ m` is bound by the single relation
`κᴴ gᴴ m = fᴴ`.  Taking `f = ‖ν‖·(b·a)` and `g = ‖ν‖·b` at the equatorial direction
`d = ν/‖ν‖`, the gauge `κ = Ω(seamPoint)` -- *the same gauge as in `LIXClutching`, not a
conjugated one* -- forces

```text
m = b(d) · Ω(seamPoint) · Ω(d)ᴴ · b(d)ᴴ
```

and on the collar `t ≤ -1/2`, where the seam parameter plateaus at `1` and
`seamPoint = d`, this collapses to `b(d) b(d)ᴴ = 1`.  So `m` is *locally constant* near
the south pole, which is even cheaper than the original file's argument, and the
intermediate `g` is already the target `coneMat B ν`: no final conjugation step is
needed at all.  Putting the gauge factor on the left instead forces
`m = Ω(seamPoint)ᴴ Ω(d)ᴴ` (up to conjugation by `b(d)`), which does *not* collapse on
the collar; that version is obtained here as a corollary by conjugating the gauge,
`a·b = b·(bᴴ a b)`.

Note that `IsDiscUnitary.map_zero` is not used by the gauge lemma: unitarity and
continuity on the ball suffice, which is why the hypothesis is packaged separately as
`IsBallUnitary`.  It is used by `isDiscUnitary_discOfHomotopy`, where the value at the
centre is the whole point.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Ball unitaries -/

section BallUnitary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- A **ball unitary**: a continuous matrix field on `E` which is unitary at every point
of the closed unit ball.  This is `IsDiscUnitary` without the normalisation `Ω 0 = 1`;
the gauge lemma needs exactly this much of both of its arguments. -/
structure IsBallUnitary (Ω : E → Matrix n n ℂ) : Prop where
  continuous : Continuous Ω
  star_mul_self : ∀ y : E, ‖y‖ ≤ 1 → (Ω y)ᴴ * Ω y = 1
  mul_star_self : ∀ y : E, ‖y‖ ≤ 1 → Ω y * (Ω y)ᴴ = 1

theorem isBallUnitary_of_isDiscUnitary {Ω : E → Matrix n n ℂ} (h : IsDiscUnitary Ω) :
    IsBallUnitary Ω :=
  ⟨h.continuous, h.star_mul_self, h.mul_star_self⟩

/-- The pointwise product of two ball unitaries is a ball unitary. -/
theorem IsBallUnitary.mul {B Ω : E → Matrix n n ℂ} (hB : IsBallUnitary B)
    (hΩ : IsBallUnitary Ω) : IsBallUnitary fun y => B y * Ω y where
  continuous := hB.continuous.matrix_mul hΩ.continuous
  star_mul_self := fun y hy =>
    (unitary_mul_unitary (hB.star_mul_self y hy) (hB.mul_star_self y hy)
      (hΩ.star_mul_self y hy) (hΩ.mul_star_self y hy)).1
  mul_star_self := fun y hy =>
    (unitary_mul_unitary (hB.star_mul_self y hy) (hB.mul_star_self y hy)
      (hΩ.star_mul_self y hy) (hΩ.mul_star_self y hy)).2

/-- The pointwise adjoint of a ball unitary is a ball unitary. -/
theorem IsBallUnitary.star {Ω : E → Matrix n n ℂ} (hΩ : IsBallUnitary Ω) :
    IsBallUnitary fun y => (Ω y)ᴴ where
  continuous := hΩ.continuous.matrix_conjTranspose
  star_mul_self := fun y hy => by
    rw [Matrix.conjTranspose_conjTranspose]; exact hΩ.mul_star_self y hy
  mul_star_self := fun y hy => by
    rw [Matrix.conjTranspose_conjTranspose]; exact hΩ.star_mul_self y hy

end BallUnitary

/-! ## Two scalar helpers -/

section Scalars

theorem star_ofReal_c (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  simp [Complex.conj_ofReal]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real multiple of a unitary is a clutching datum for the matching height. -/
theorem isClutchDatum_smul {s r : ℝ} {A : Matrix n n ℂ} (hr : r * r = 1 - s ^ 2)
    (h1 : Aᴴ * A = 1) (h2 : A * Aᴴ = 1) : IsClutchDatum s (((r : ℝ) : ℂ) • A) := by
  have hcast : ((r : ℝ) : ℂ) * ((r : ℝ) : ℂ) = 1 - ((s : ℝ) : ℂ) ^ 2 := by
    have h := congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) hr
    push_cast at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, star_ofReal_c, Matrix.smul_mul, Matrix.mul_smul, h1,
      smul_smul, hcast]
  · rw [Matrix.conjTranspose_smul, star_ofReal_c, Matrix.smul_mul, Matrix.mul_smul, h2,
      smul_smul, hcast]

/-- Unitarity of a product, in paired form. -/
theorem unit_mul {A C : Matrix n n ℂ} (hA : Aᴴ * A = 1 ∧ A * Aᴴ = 1)
    (hC : Cᴴ * C = 1 ∧ C * Cᴴ = 1) : (A * C)ᴴ * (A * C) = 1 ∧ (A * C) * (A * C)ᴴ = 1 :=
  unitary_mul_unitary hA.1 hA.2 hC.1 hC.2

/-- Unitarity of an adjoint, in paired form. -/
theorem unit_star {A : Matrix n n ℂ} (hA : Aᴴ * A = 1 ∧ A * Aᴴ = 1) :
    (Aᴴ)ᴴ * Aᴴ = 1 ∧ Aᴴ * (Aᴴ)ᴴ = 1 := by
  rw [Matrix.conjTranspose_conjTranspose]
  exact ⟨hA.2, hA.1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two clutching functions agreeing on the unit sphere have the same cone. -/
theorem coneMat_congr {W W' : E → Matrix n n ℂ} (h : ∀ y : E, ‖y‖ = 1 → W y = W' y)
    (y : E) : coneMat W y = coneMat W' y := by
  rcases eq_or_ne y 0 with hy | hy
  · rw [coneMat_def, coneMat_def, hy, norm_zero]
    simp
  · rw [coneMat_def, coneMat_def, h _ (by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)])]

end Scalars

/-! ## The gauge lemma -/

section Gauge

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n]
  {t : X → ℝ} {ν : X → E} {B Ω : E → Matrix n n ℂ}

/-- The seam correction of the gauge lemma: `b(d) · Ω(seamPoint) · Ω(d)ᴴ · b(d)ᴴ`.
On the collar `t ≤ -1/2` the seam parameter plateaus at `1`, so `seamPoint = d` and this
is the constant `1`. -/
def gaugeCorr (t : X → ℝ) (ν : X → E) (B Ω : E → Matrix n n ℂ) (x : X) : Matrix n n ℂ :=
  B (chartDir ν x) * Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ

theorem gaugeCorr_def (x : X) :
    gaugeCorr t ν B Ω x =
      B (chartDir ν x) * Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ *
        (B (chartDir ν x))ᴴ := rfl

/-- The cone of a pointwise product, at an equatorial point. -/
theorem coneMat_mul_apply (x : X) :
    coneMat (fun y => B y * Ω y) (ν x)
      = ((‖ν x‖ : ℝ) : ℂ) • (B (chartDir ν x) * Ω (chartDir ν x)) := rfl

/-- **On the collar the seam correction is the identity.** -/
theorem gaugeCorr_eq_one_of_lt (hB : IsBallUnitary B) (hΩ : IsBallUnitary Ω) {x : X}
    (hx : t x < -(1 / 2)) : gaugeCorr t ν B Ω x = 1 := by
  have hsp : seamParam (t x) = 1 := seamParam_of_le (le_of_lt hx)
  have hpt : seamPoint t ν x = chartDir ν x := by
    rw [seamPoint_def, hsp, one_mul, chartDir_def]
  rw [gaugeCorr_def, hpt, Matrix.mul_assoc (B (chartDir ν x)),
    hΩ.mul_star_self _ (norm_chartDir_le_one ν x), Matrix.mul_one,
    hB.mul_star_self _ (norm_chartDir_le_one ν x)]

/-- The seam correction is unitary. -/
theorem unit_gaugeCorr (hB : IsBallUnitary B) (hΩ : IsBallUnitary Ω) (x : X) :
    (gaugeCorr t ν B Ω x)ᴴ * gaugeCorr t ν B Ω x = 1 ∧
      gaugeCorr t ν B Ω x * (gaugeCorr t ν B Ω x)ᴴ = 1 := by
  have hBd : (B (chartDir ν x))ᴴ * B (chartDir ν x) = 1 ∧
      B (chartDir ν x) * (B (chartDir ν x))ᴴ = 1 :=
    ⟨hB.star_mul_self _ (norm_chartDir_le_one ν x),
      hB.mul_star_self _ (norm_chartDir_le_one ν x)⟩
  have hΩd : (Ω (chartDir ν x))ᴴ * Ω (chartDir ν x) = 1 ∧
      Ω (chartDir ν x) * (Ω (chartDir ν x))ᴴ = 1 :=
    ⟨hΩ.star_mul_self _ (norm_chartDir_le_one ν x),
      hΩ.mul_star_self _ (norm_chartDir_le_one ν x)⟩
  have hΩs : (Ω (seamPoint t ν x))ᴴ * Ω (seamPoint t ν x) = 1 ∧
      Ω (seamPoint t ν x) * (Ω (seamPoint t ν x))ᴴ = 1 :=
    ⟨hΩ.star_mul_self _ (norm_seamPoint_le_one t ν x),
      hΩ.mul_star_self _ (norm_seamPoint_le_one t ν x)⟩
  exact unit_mul (unit_mul (unit_mul hBd hΩs) (unit_star hΩd)) (unit_star hBd)

/-- **The seam relation** for the gauge lemma, at every point and with no case split. -/
theorem gauge_seam_identity (hB : IsBallUnitary B) (hΩ : IsBallUnitary Ω) (x : X) :
    (Ω (seamPoint t ν x))ᴴ * (coneMat B (ν x))ᴴ * gaugeCorr t ν B Ω x
      = (coneMat (fun y => B y * Ω y) (ν x))ᴴ := by
  have hBd : (B (chartDir ν x))ᴴ * B (chartDir ν x) = 1 :=
    hB.star_mul_self _ (norm_chartDir_le_one ν x)
  have hΩs : (Ω (seamPoint t ν x))ᴴ * Ω (seamPoint t ν x) = 1 :=
    hΩ.star_mul_self _ (norm_seamPoint_le_one t ν x)
  have hg : (coneMat B (ν x))ᴴ = ((‖ν x‖ : ℝ) : ℂ) • (B (chartDir ν x))ᴴ := by
    rw [coneMat_apply_equator, Matrix.conjTranspose_smul, star_ofReal_c]
  have hf : (coneMat (fun y => B y * Ω y) (ν x))ᴴ
      = ((‖ν x‖ : ℝ) : ℂ) • ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ) := by
    rw [coneMat_mul_apply, Matrix.conjTranspose_smul, star_ofReal_c,
      Matrix.conjTranspose_mul]
  have hinner : (Ω (seamPoint t ν x))ᴴ * (B (chartDir ν x))ᴴ * gaugeCorr t ν B Ω x
      = (Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ := by
    rw [gaugeCorr_def]
    calc (Ω (seamPoint t ν x))ᴴ * (B (chartDir ν x))ᴴ *
          (B (chartDir ν x) * Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ *
            (B (chartDir ν x))ᴴ)
        = (Ω (seamPoint t ν x))ᴴ * ((B (chartDir ν x))ᴴ * B (chartDir ν x)) *
            (Ω (seamPoint t ν x) * ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ)) := by
          simp only [Matrix.mul_assoc]
      _ = (Ω (seamPoint t ν x))ᴴ * Ω (seamPoint t ν x) *
            ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ) := by
          rw [hBd, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ := by rw [hΩs, Matrix.one_mul]
  rw [hg, hf, Matrix.mul_smul, Matrix.smul_mul, hinner]

/-- The four blocks of the gauge seam isometry, damped. -/
theorem gaugeSeam_eq_fromBlocks (x : X) :
    seamMat (t x) (coneMat (fun y => B y * Ω y) (ν x)) (coneMat B (ν x))
        (Ω (seamPoint t ν x)) (gaugeCorr t ν B Ω x)
      = Matrix.fromBlocks
          ((((1 + t x) / 2 : ℝ) : ℂ) • Ω (seamPoint t ν x))
          (((‖ν x‖ / 2 : ℝ) : ℂ) •
            (Ω (seamPoint t ν x) * ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ)))
          (((‖ν x‖ / 2 : ℝ) : ℂ) • (B (chartDir ν x) * Ω (seamPoint t ν x)))
          ((((1 - t x) / 2 : ℝ) : ℂ) • gaugeCorr t ν B Ω x) := by
  have hhalf : (1 / 2 : ℂ) * ((‖ν x‖ : ℝ) : ℂ) = ((‖ν x‖ / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [seamMat, Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, rfl⟩
  · have hf : (coneMat (fun y => B y * Ω y) (ν x))ᴴ
        = ((‖ν x‖ : ℝ) : ℂ) • ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ) := by
      rw [coneMat_mul_apply, Matrix.conjTranspose_smul, star_ofReal_c,
        Matrix.conjTranspose_mul]
    rw [hf, Matrix.mul_smul, smul_smul, hhalf]
  · rw [coneMat_apply_equator, Matrix.smul_mul, smul_smul, hhalf]

/-- **The gauge lemma.**  Changing a clutching function on the right by a factor that is
continuous and unitary on the closed unit ball does not change the clutched projection up
to Murray--von Neumann equivalence of continuous fields. -/
theorem exists_partialIsometry_of_gauge_right (hc : IsSuspensionChart t ν)
    (hB : IsBallUnitary B) (hΩ : IsBallUnitary Ω) :
    ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x = clutchMat (t x) (coneMat (fun y => B y * Ω y) (ν x))) ∧
      (∀ x, V x * (V x)ᴴ = clutchMat (t x) (coneMat B (ν x))) := by
  classical
  have hnorm : ∀ x : X, ‖ν x‖ * ‖ν x‖ = 1 - t x ^ 2 := by
    intro x
    nlinarith [hc.sphere x]
  have hBd : ∀ x : X, (B (chartDir ν x))ᴴ * B (chartDir ν x) = 1 ∧
      B (chartDir ν x) * (B (chartDir ν x))ᴴ = 1 := fun x =>
    ⟨hB.star_mul_self _ (norm_chartDir_le_one ν x),
      hB.mul_star_self _ (norm_chartDir_le_one ν x)⟩
  have hΩd : ∀ x : X, (Ω (chartDir ν x))ᴴ * Ω (chartDir ν x) = 1 ∧
      Ω (chartDir ν x) * (Ω (chartDir ν x))ᴴ = 1 := fun x =>
    ⟨hΩ.star_mul_self _ (norm_chartDir_le_one ν x),
      hΩ.mul_star_self _ (norm_chartDir_le_one ν x)⟩
  have hΩs : ∀ x : X, (Ω (seamPoint t ν x))ᴴ * Ω (seamPoint t ν x) = 1 ∧
      Ω (seamPoint t ν x) * (Ω (seamPoint t ν x))ᴴ = 1 := fun x =>
    ⟨hΩ.star_mul_self _ (norm_seamPoint_le_one t ν x),
      hΩ.mul_star_self _ (norm_seamPoint_le_one t ν x)⟩
  -- the two clutching data
  have hfd : ∀ x : X, IsClutchDatum (t x) (coneMat (fun y => B y * Ω y) (ν x)) := by
    intro x
    rw [coneMat_mul_apply]
    exact isClutchDatum_smul (hnorm x) (unit_mul (hBd x) (hΩd x)).1
      (unit_mul (hBd x) (hΩd x)).2
  have hgd : ∀ x : X, IsClutchDatum (t x) (coneMat B (ν x)) := by
    intro x
    rw [coneMat_apply_equator]
    exact isClutchDatum_smul (hnorm x) (hBd x).1 (hBd x).2
  have hm := unit_gaugeCorr (t := t) (ν := ν) hB hΩ
  have hseam := gauge_seam_identity (t := t) (ν := ν) hB hΩ
  refine ⟨fun x => seamMat (t x) (coneMat (fun y => B y * Ω y) (ν x)) (coneMat B (ν x))
    (Ω (seamPoint t ν x)) (gaugeCorr t ν B Ω x), ?_, ?_, ?_⟩
  · -- continuity, block by block
    have hb1 : ∀ (x : X) (i j : n), ‖Ω (seamPoint t ν x) i j‖ ≤ 1 := fun x =>
      norm_entry_le_one (hΩs x).1
    have hb2 : ∀ (x : X) (i j : n),
        ‖(Ω (seamPoint t ν x) * ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ)) i j‖ ≤ 1 :=
      fun x => norm_entry_le_one
        (unit_mul (hΩs x) (unit_mul (unit_star (hΩd x)) (unit_star (hBd x)))).1
    have hb3 : ∀ (x : X) (i j : n),
        ‖(B (chartDir ν x) * Ω (seamPoint t ν x)) i j‖ ≤ 1 := fun x =>
      norm_entry_le_one (unit_mul (hBd x) (hΩs x)).1
    have hb4 : ∀ (x : X) (i j : n), ‖gaugeCorr t ν B Ω x i j‖ ≤ 1 := fun x =>
      norm_entry_le_one (hm x).1
    have hblock1 : Continuous fun x : X =>
        ((((1 + t x) / 2 : ℝ)) : ℂ) • Ω (seamPoint t ν x) := by
      refine continuous_damped (U := {x : X | t x ≠ -1})
        (isOpen_compl_singleton.preimage hc.continuous_height)
        ((continuous_const.add hc.continuous_height).div_const 2) ?_ hb1 ?_
      · exact continuousOn_of_forall_continuousAt fun x hx =>
          hΩ.continuous.continuousAt.comp (continuousAt_seamPoint hc hx)
      · intro x hx
        have h1 : t x = -1 := by simpa using hx
        show (1 + t x) / 2 = 0
        rw [h1]
        norm_num
    have hblock2 : Continuous fun x : X => ((‖ν x‖ / 2 : ℝ) : ℂ) •
        (Ω (seamPoint t ν x) * ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ)) := by
      refine continuous_damped (U := {x : X | ν x ≠ 0}) (isOpen_equator_ne hc)
        (hc.continuous_equator.norm.div_const 2) ?_ hb2 ?_
      · refine continuousOn_of_forall_continuousAt fun x hx => ?_
        have hA : ContinuousAt (fun y : X => Ω (seamPoint t ν y)) x :=
          hΩ.continuous.continuousAt.comp (continuousAt_seamPoint_of_ne hc hx)
        have hC : ContinuousAt (fun y : X => (Ω (chartDir ν y))ᴴ) x :=
          (hΩ.continuous.continuousAt.comp (continuousAt_chartDir hc hx)).star
        have hD : ContinuousAt (fun y : X => (B (chartDir ν y))ᴴ) x :=
          (hB.continuous.continuousAt.comp (continuousAt_chartDir hc hx)).star
        exact hA.mul (hC.mul hD)
      · intro x hx
        have h0 : ν x = 0 := by simpa using hx
        show ‖ν x‖ / 2 = 0
        rw [h0]
        norm_num
    have hblock3 : Continuous fun x : X => ((‖ν x‖ / 2 : ℝ) : ℂ) •
        (B (chartDir ν x) * Ω (seamPoint t ν x)) := by
      refine continuous_damped (U := {x : X | ν x ≠ 0}) (isOpen_equator_ne hc)
        (hc.continuous_equator.norm.div_const 2) ?_ hb3 ?_
      · refine continuousOn_of_forall_continuousAt fun x hx => ?_
        have hA : ContinuousAt (fun y : X => B (chartDir ν y)) x :=
          hB.continuous.continuousAt.comp (continuousAt_chartDir hc hx)
        have hC : ContinuousAt (fun y : X => Ω (seamPoint t ν y)) x :=
          hΩ.continuous.continuousAt.comp (continuousAt_seamPoint_of_ne hc hx)
        exact hA.mul hC
      · intro x hx
        have h0 : ν x = 0 := by simpa using hx
        show ‖ν x‖ / 2 = 0
        rw [h0]
        norm_num
    have hblock4 : Continuous fun x : X =>
        ((((1 - t x) / 2 : ℝ)) : ℂ) • gaugeCorr t ν B Ω x := by
      refine continuous_damped (U := {x : X | t x ≠ 1})
        (isOpen_compl_singleton.preimage hc.continuous_height)
        ((continuous_const.sub hc.continuous_height).div_const 2) ?_ hb4 ?_
      · refine continuousOn_of_forall_continuousAt fun x hx => ?_
        rcases eq_or_ne (ν x) 0 with h | h
        · have ht1 : t x = -1 := by
            rcases height_eq_of_equator_zero hc h with h1 | h1
            · exact absurd h1 hx
            · exact h1
          have hW : IsOpen {y : X | t y < -(1 / 2 : ℝ)} :=
            isOpen_lt hc.continuous_height continuous_const
          have hmem : x ∈ {y : X | t y < -(1 / 2 : ℝ)} := by
            show t x < -(1 / 2 : ℝ)
            rw [ht1]
            norm_num
          have heq : Set.EqOn (fun _ : X => (1 : Matrix n n ℂ)) (gaugeCorr t ν B Ω)
              {y : X | t y < -(1 / 2 : ℝ)} := fun y hy =>
            (gaugeCorr_eq_one_of_lt hB hΩ hy).symm
          exact ContinuousAt.congr continuousAt_const
            (Filter.eventuallyEq_of_mem (hW.mem_nhds hmem) heq)
        · have hA : ContinuousAt (fun y : X => B (chartDir ν y)) x :=
            hB.continuous.continuousAt.comp (continuousAt_chartDir hc h)
          have hC : ContinuousAt (fun y : X => Ω (seamPoint t ν y)) x :=
            hΩ.continuous.continuousAt.comp (continuousAt_seamPoint_of_ne hc h)
          have hD : ContinuousAt (fun y : X => (Ω (chartDir ν y))ᴴ) x :=
            (hΩ.continuous.continuousAt.comp (continuousAt_chartDir hc h)).star
          have hF : ContinuousAt (fun y : X => (B (chartDir ν y))ᴴ) x :=
            (hB.continuous.continuousAt.comp (continuousAt_chartDir hc h)).star
          exact ((hA.mul hC).mul hD).mul hF
      · intro x hx
        have h1 : t x = 1 := by simpa using hx
        show (1 - t x) / 2 = 0
        rw [h1]
        norm_num
    have hrw : (fun x : X => seamMat (t x) (coneMat (fun y => B y * Ω y) (ν x))
        (coneMat B (ν x)) (Ω (seamPoint t ν x)) (gaugeCorr t ν B Ω x))
        = fun x : X => Matrix.fromBlocks
          ((((1 + t x) / 2 : ℝ) : ℂ) • Ω (seamPoint t ν x))
          (((‖ν x‖ / 2 : ℝ) : ℂ) •
            (Ω (seamPoint t ν x) * ((Ω (chartDir ν x))ᴴ * (B (chartDir ν x))ᴴ)))
          (((‖ν x‖ / 2 : ℝ) : ℂ) • (B (chartDir ν x) * Ω (seamPoint t ν x)))
          ((((1 - t x) / 2 : ℝ) : ℂ) • gaugeCorr t ν B Ω x) := by
      funext x
      exact gaugeSeam_eq_fromBlocks x
    rw [hrw]
    exact continuous_fromBlocks hblock1 hblock2 hblock3 hblock4
  · exact fun x => seamMat_conjTranspose_mul_self (hfd x) (hgd x) (hΩs x).1 (hm x).1 (hseam x)
  · exact fun x => seamMat_mul_conjTranspose (hfd x) (hgd x) (hΩs x).2 (hm x).2 (hseam x)

/-- **The gauge lemma, factor on the left.**  Obtained from the right-hand version by
conjugating the gauge, `a·b = b·(bᴴ a b)`; the conjugate of a ball unitary by a ball
unitary is again one. -/
theorem exists_partialIsometry_of_gauge_left (hc : IsSuspensionChart t ν)
    (hB : IsBallUnitary B) (hΩ : IsBallUnitary Ω) :
    ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x = clutchMat (t x) (coneMat (fun y => Ω y * B y) (ν x))) ∧
      (∀ x, V x * (V x)ᴴ = clutchMat (t x) (coneMat B (ν x))) := by
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_of_gauge_right (B := B)
      (Ω := fun y => (B y)ᴴ * (Ω y * B y)) hc hB (hB.star.mul (hΩ.mul hB))
  refine ⟨V, hVc, fun x => ?_, hV2⟩
  rw [hV1 x]
  congr 1
  refine coneMat_congr (fun y hy => ?_) (ν x)
  show B y * ((B y)ᴴ * (Ω y * B y)) = Ω y * B y
  rw [← Matrix.mul_assoc, hB.mul_star_self y (le_of_eq hy), Matrix.one_mul]

end Gauge

/-! ## The disc form of a null-homotopy -/

section DiscForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The homotopy parameter read off the radius, with a **plateau** on the inner
half-ball: `0` for `r ≤ 1/2` and `1` at `r = 1`. -/
def discParam (r : ℝ) : ℝ := min 1 (max 0 (2 * r - 1))

theorem discParam_nonneg (r : ℝ) : 0 ≤ discParam r :=
  le_min (by norm_num) (le_max_left _ _)

theorem discParam_le_one (r : ℝ) : discParam r ≤ 1 := min_le_left _ _

theorem discParam_of_le {r : ℝ} (hr : r ≤ 1 / 2) : discParam r = 0 := by
  have h : max 0 (2 * r - 1) = 0 := max_eq_left (by linarith)
  rw [discParam, h, min_eq_right (by norm_num)]

theorem discParam_one : discParam 1 = 1 := by
  rw [discParam, show (2 : ℝ) * 1 - 1 = 1 by norm_num, max_eq_right (by norm_num),
    min_self]

theorem continuous_discParam : Continuous discParam :=
  continuous_const.min (continuous_const.max ((continuous_const.mul continuous_id).sub
    continuous_const))

/-- **The disc form of a null-homotopy.**  `H` is a homotopy on the closed unit ball
starting at the constant `1`; `discOfHomotopy H` reads the parameter off the radius, with
a plateau which makes it literally constant on the inner half-ball. -/
def discOfHomotopy (H : ℝ → E → Matrix n n ℂ) (y : E) : Matrix n n ℂ :=
  H (discParam ‖y‖) ((‖y‖)⁻¹ • y)

theorem discOfHomotopy_apply_sphere (H : ℝ → E → Matrix n n ℂ) {y : E} (hy : ‖y‖ = 1) :
    discOfHomotopy H y = H 1 y := by
  rw [discOfHomotopy, hy, discParam_one, inv_one, one_smul]

/-- **A plateaued null-homotopy is a disc unitary.**  Continuity at the centre is free:
the map is the constant `1` on the whole inner half-ball, so no uniformity in the
direction is needed and `E` may be infinite-dimensional. -/
theorem isDiscUnitary_discOfHomotopy {H : ℝ → E → Matrix n n ℂ}
    (hH : Continuous fun p : ℝ × E => H p.1 p.2)
    (hH0 : ∀ y : E, ‖y‖ ≤ 1 → H 0 y = 1)
    (hHu : ∀ (θ : ℝ) (y : E), 0 ≤ θ → θ ≤ 1 → ‖y‖ ≤ 1 → (H θ y)ᴴ * H θ y = 1)
    (hHu' : ∀ (θ : ℝ) (y : E), 0 ≤ θ → θ ≤ 1 → ‖y‖ ≤ 1 → H θ y * (H θ y)ᴴ = 1) :
    IsDiscUnitary (discOfHomotopy H) where
  continuous := by
    rw [continuous_iff_continuousAt]
    intro y₀
    rcases eq_or_ne y₀ 0 with h | h
    · have hW : IsOpen {y : E | ‖y‖ < 1 / 2} := isOpen_lt continuous_norm continuous_const
      have hmem : y₀ ∈ {y : E | ‖y‖ < 1 / 2} := by
        show ‖y₀‖ < 1 / 2
        rw [h, norm_zero]
        norm_num
      have heq : Set.EqOn (fun _ : E => (1 : Matrix n n ℂ)) (discOfHomotopy H)
          {y : E | ‖y‖ < 1 / 2} := by
        intro y hy
        have hy' : ‖y‖ ≤ 1 / 2 := le_of_lt hy
        rw [discOfHomotopy, discParam_of_le hy', hH0 _ (norm_dir_le_one y)]
      exact ContinuousAt.congr continuousAt_const
        (Filter.eventuallyEq_of_mem (hW.mem_nhds hmem) heq)
    · have h1 : ContinuousAt (fun y : E => discParam ‖y‖) y₀ :=
        (continuous_discParam.comp continuous_norm).continuousAt
      have h2 : ContinuousAt (fun y : E => (‖y‖)⁻¹ • y) y₀ := by
        have hinv : ContinuousAt (fun y : E => (‖y‖)⁻¹) y₀ :=
          ContinuousAt.inv₀ continuous_norm.continuousAt (norm_ne_zero_iff.mpr h)
        exact hinv.smul continuousAt_id
      have h3 : ContinuousAt (fun y : E => ((discParam ‖y‖ : ℝ), (‖y‖)⁻¹ • y)) y₀ :=
        h1.prodMk h2
      exact hH.continuousAt.comp h3
  map_zero := by
    rw [discOfHomotopy, norm_zero, discParam_of_le (by norm_num), smul_zero,
      hH0 0 (by rw [norm_zero]; norm_num)]
  star_mul_self := fun y _ =>
    hHu _ _ (discParam_nonneg _) (discParam_le_one _) (norm_dir_le_one y)
  mul_star_self := fun y _ =>
    hHu' _ _ (discParam_nonneg _) (discParam_le_one _) (norm_dir_le_one y)

end DiscForm

/-! ## Homotopy invariance of clutching -/

section HomotopyInvariance

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n]
  {t : X → ℝ} {ν : X → E}

/-- **Homotopy invariance of clutching.**  If `W₁` differs from `W₀` on the unit sphere
by a factor which is connected to the identity through unitaries of the closed ball, then
the two clutched projections are Murray--von Neumann equivalent through an explicit
continuous partial isometry.

This is the export of the powers lane: it turns any explicit homotopy of clutching
functions -- in particular the Eckmann--Hilton homotopy `u^k ≃ u ∘ ψ_k` -- into an
equality of clutched projections, with no functional calculus and no compactness. -/
theorem exists_partialIsometry_of_homotopy (hc : IsSuspensionChart t ν)
    {W₀ W₁ : E → Matrix n n ℂ} (hW₀ : IsBallUnitary W₀)
    {H : ℝ → E → Matrix n n ℂ}
    (hH : Continuous fun p : ℝ × E => H p.1 p.2)
    (hH0 : ∀ y : E, ‖y‖ ≤ 1 → H 0 y = 1)
    (hHu : ∀ (θ : ℝ) (y : E), 0 ≤ θ → θ ≤ 1 → ‖y‖ ≤ 1 → (H θ y)ᴴ * H θ y = 1)
    (hHu' : ∀ (θ : ℝ) (y : E), 0 ≤ θ → θ ≤ 1 → ‖y‖ ≤ 1 → H θ y * (H θ y)ᴴ = 1)
    (hH1 : ∀ y : E, ‖y‖ = 1 → W₁ y = W₀ y * H 1 y) :
    ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x = clutchMat (t x) (coneMat W₁ (ν x))) ∧
      (∀ x, V x * (V x)ᴴ = clutchMat (t x) (coneMat W₀ (ν x))) := by
  have hΩ : IsBallUnitary (discOfHomotopy H) :=
    isBallUnitary_of_isDiscUnitary (isDiscUnitary_discOfHomotopy hH hH0 hHu hHu')
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_of_gauge_right (B := W₀) (Ω := discOfHomotopy H) hc hW₀ hΩ
  refine ⟨V, hVc, fun x => ?_, hV2⟩
  rw [hV1 x]
  congr 1
  refine coneMat_congr (fun y hy => ?_) (ν x)
  show W₀ y * discOfHomotopy H y = W₁ y
  rw [discOfHomotopy_apply_sphere H hy, ← hH1 y hy]

end HomotopyInvariance

end

end Powers
end LIX
end GroupApproximation
