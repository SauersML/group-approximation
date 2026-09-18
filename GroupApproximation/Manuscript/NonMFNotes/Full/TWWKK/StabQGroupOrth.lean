import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.NonUnitalHomotopy

/-!
# Orthogonal sums and Cuntz-stable C⋆-algebras

This file isolates the part of the Cuntz picture of Kasparov theory (J. Cuntz, *A new look at
KK-theory*, K-Theory 1 (1987) 31--51, §1; Blackadar, *K-Theory for Operator Algebras*, §17.8)
that concerns the target algebra only.

* `NOrth u u'`: two `⋆`-homomorphisms with mutually orthogonal ranges;
* `orthSum u u' h`: their pointwise sum, again a `⋆`-homomorphism;
* `CuntzStable E`: the structure a stable algebra `E ≅ 𝒦 ⊗ X` carries.  One has two
  orthogonal "Cuntz isometry" endomorphisms `ι₁ = Ad s₁`, `ι₂ = Ad s₂`, with `ι₁` homotopic to the
  identity, and a rotation path `rot t = Ad (cos t · s₁ + sin t · s₂)` from `ι₁` to `ι₂`.
  The rotation path is orthogonal to `ι₁` on orthogonal elements;
* `CuntzStable.sum`: the Cuntz sum `x ⊕ x' = ι₁ ∘ x + ι₂ ∘ x'`, which respects homotopy in each
  variable;
* `CuntzStable.nHomotopic_orthSum_sum`: an orthogonal sum is homotopic to the Cuntz sum.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(Tikuisis--White--Winter).  This is infrastructure for `WO-TWWKK-B` (`stabQGroups`,
`stabQ_compBilinear`).
-/

namespace GroupApproximation.Full.TWWKK

universe u v

noncomputable section

section Orth

variable {D : Type u} {E : Type v} {E' : Type*} {D' : Type*}
variable [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra E']
  [NonUnitalCStarAlgebra D']

/-- Two `⋆`-homomorphisms with mutually orthogonal ranges. -/
def NOrth (u u' : D →⋆ₙₐ[ℂ] E) : Prop :=
  ∀ d d' : D, u d * u' d' = 0 ∧ u' d' * u d = 0

theorem NOrth.symm {u u' : D →⋆ₙₐ[ℂ] E} (h : NOrth u u') : NOrth u' u :=
  fun d d' => ⟨(h d' d).2, (h d' d).1⟩

theorem NOrth.comp_left (y : E →⋆ₙₐ[ℂ] E') {u u' : D →⋆ₙₐ[ℂ] E} (h : NOrth u u') :
    NOrth (y.comp u) (y.comp u') := by
  intro d d'
  constructor
  · show y (u d) * y (u' d') = 0
    rw [← map_mul, (h d d').1, map_zero]
  · show y (u' d') * y (u d) = 0
    rw [← map_mul, (h d d').2, map_zero]

theorem NOrth.comp_right {u u' : D →⋆ₙₐ[ℂ] E} (h : NOrth u u') (z : D' →⋆ₙₐ[ℂ] D) :
    NOrth (u.comp z) (u'.comp z) :=
  fun d d' => h (z d) (z d')

/-- The **orthogonal sum** of two `⋆`-homomorphisms with orthogonal ranges. -/
def orthSum (u u' : D →⋆ₙₐ[ℂ] E) (h : NOrth u u') : D →⋆ₙₐ[ℂ] E where
  toFun d := u d + u' d
  map_smul' c d := by
    show u (c • d) + u' (c • d) = c • (u d + u' d)
    rw [map_smul, map_smul, smul_add]
  map_zero' := by
    show u 0 + u' 0 = 0
    rw [map_zero, map_zero, add_zero]
  map_add' d d' := by
    show u (d + d') + u' (d + d') = (u d + u' d) + (u d' + u' d')
    rw [map_add, map_add]
    exact add_add_add_comm _ _ _ _
  map_mul' d d' := by
    show u (d * d') + u' (d * d') = (u d + u' d) * (u d' + u' d')
    rw [map_mul, map_mul, add_mul, mul_add, mul_add, (h d d').1, (h d' d).2, add_zero, zero_add]
  map_star' d := by
    show u (star d) + u' (star d) = star (u d + u' d)
    rw [map_star, map_star, star_add]

theorem orthSum_apply (u u' : D →⋆ₙₐ[ℂ] E) (h : NOrth u u') (d : D) :
    orthSum u u' h d = u d + u' d :=
  rfl

theorem orthSum_comm (u u' : D →⋆ₙₐ[ℂ] E) (h : NOrth u u') :
    orthSum u u' h = orthSum u' u h.symm :=
  NonUnitalStarAlgHom.ext fun d => add_comm (u d) (u' d)

theorem comp_orthSum (y : E →⋆ₙₐ[ℂ] E') (u u' : D →⋆ₙₐ[ℂ] E) (h : NOrth u u') :
    y.comp (orthSum u u' h) = orthSum (y.comp u) (y.comp u') (NOrth.comp_left y h) :=
  NonUnitalStarAlgHom.ext fun d => map_add y (u d) (u' d)

theorem orthSum_comp (u u' : D →⋆ₙₐ[ℂ] E) (h : NOrth u u') (z : D' →⋆ₙₐ[ℂ] D) :
    (orthSum u u' h).comp z = orthSum (u.comp z) (u'.comp z) (h.comp_right z) :=
  NonUnitalStarAlgHom.ext fun _ => rfl

theorem NOrth.orthSum_left {u u' w : D →⋆ₙₐ[ℂ] E} (h : NOrth u u') (hu : NOrth u w)
    (hu' : NOrth u' w) : NOrth (orthSum u u' h) w := by
  intro d d'
  constructor
  · show (u d + u' d) * w d' = 0
    rw [add_mul, (hu d d').1, (hu' d d').1, add_zero]
  · show w d' * (u d + u' d) = 0
    rw [mul_add, (hu d d').2, (hu' d d').2, add_zero]

theorem NOrth.orthSum_right {u w w' : D →⋆ₙₐ[ℂ] E} (h : NOrth w w') (hw : NOrth u w)
    (hw' : NOrth u w') : NOrth u (orthSum w w' h) := by
  intro d d'
  constructor
  · show u d * (w d' + w' d') = 0
    rw [mul_add, (hw d d').1, (hw' d d').1, add_zero]
  · show (w d' + w' d') * u d = 0
    rw [add_mul, (hw d d').2, (hw' d d').2, add_zero]

/-- Composing with the zero homomorphism on the right gives zero. -/
theorem comp_zero_hom (y : E →⋆ₙₐ[ℂ] E') :
    y.comp (0 : D →⋆ₙₐ[ℂ] E) = 0 :=
  NonUnitalStarAlgHom.ext fun _ => map_zero y

end Orth

/-- **Cuntz-stable C⋆-algebras.**  The data a stable algebra `E ≅ 𝒦 ⊗ X` carries for the
Cuntz sum (Cuntz 1987, §1; Blackadar 17.8).  `ι₁ = Ad s₁` and `ι₂ = Ad s₂` for isometries
`s₁, s₂ ∈ M(𝒦)` with `s₁ s₁* + s₂ s₂* = 1`.  `ι₁` is homotopic to the identity (an isometry is
strictly connected to `1`).  `rot t = Ad (cos (πt/2) s₁ + sin (πt/2) s₂)` joins `ι₁` to `ι₂`.
Since `s₁* s₂ = 0`, one has `ι₁ e · rot t e' = cos · s₁ e e' (…)*`, and this vanishes when
`e e' = 0`. -/
structure CuntzStable (E : Type v) [NonUnitalCStarAlgebra E] where
  /-- The first Cuntz isometry endomorphism. -/
  ι₁ : E →⋆ₙₐ[ℂ] E
  /-- The second Cuntz isometry endomorphism. -/
  ι₂ : E →⋆ₙₐ[ℂ] E
  /-- The two ranges are orthogonal. -/
  orth : NOrth ι₁ ι₂
  /-- `ι₁` is homotopic to the identity. -/
  ι₁_nHomotopic : NHomotopic ι₁ (NonUnitalStarAlgHom.id ℂ E)
  /-- The rotation path from `ι₁` to `ι₂`. -/
  rot : ℝ → (E →⋆ₙₐ[ℂ] E)
  /-- The rotation path is pointwise continuous. -/
  rot_continuous : ∀ e : E, Continuous fun t : ℝ => rot t e
  rot_zero : rot 0 = ι₁
  rot_one : rot 1 = ι₂
  /-- The rotation path stays orthogonal to `ι₁` on orthogonal elements (left). -/
  rot_orth_left : ∀ (t : ℝ) (e e' : E), e * e' = 0 → ι₁ e * rot t e' = 0
  /-- The rotation path stays orthogonal to `ι₁` on orthogonal elements (right). -/
  rot_orth_right : ∀ (t : ℝ) (e e' : E), e' * e = 0 → rot t e' * ι₁ e = 0

namespace CuntzStable

variable {D : Type u} {E : Type v} {D' : Type*}
variable [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra D']
variable (S : CuntzStable E)

theorem sum_orth (x x' : D →⋆ₙₐ[ℂ] E) : NOrth (S.ι₁.comp x) (S.ι₂.comp x') :=
  fun d d' => S.orth (x d) (x' d')

/-- The **Cuntz sum** `x ⊕ x' = ι₁ ∘ x + ι₂ ∘ x'`. -/
def sum (x x' : D →⋆ₙₐ[ℂ] E) : D →⋆ₙₐ[ℂ] E :=
  orthSum (S.ι₁.comp x) (S.ι₂.comp x') (S.sum_orth x x')

theorem sum_apply (x x' : D →⋆ₙₐ[ℂ] E) (d : D) : S.sum x x' d = S.ι₁ (x d) + S.ι₂ (x' d) :=
  rfl

theorem sum_comp (x x' : D →⋆ₙₐ[ℂ] E) (z : D' →⋆ₙₐ[ℂ] D) :
    (S.sum x x').comp z = S.sum (x.comp z) (x'.comp z) :=
  NonUnitalStarAlgHom.ext fun _ => rfl

theorem sum_zero (x : D →⋆ₙₐ[ℂ] E) : S.sum x 0 = S.ι₁.comp x :=
  NonUnitalStarAlgHom.ext fun d => by
    show S.ι₁ (x d) + S.ι₂ ((0 : D →⋆ₙₐ[ℂ] E) d) = S.ι₁ (x d)
    rw [NonUnitalStarAlgHom.zero_apply, map_zero, add_zero]

theorem zero_sum (x : D →⋆ₙₐ[ℂ] E) : S.sum 0 x = S.ι₂.comp x :=
  NonUnitalStarAlgHom.ext fun d => by
    show S.ι₁ ((0 : D →⋆ₙₐ[ℂ] E) d) + S.ι₂ (x d) = S.ι₂ (x d)
    rw [NonUnitalStarAlgHom.zero_apply, map_zero, zero_add]

theorem nHomotopic_ι₁_comp (w : D →⋆ₙₐ[ℂ] E) : NHomotopic (S.ι₁.comp w) w := by
  have h := S.ι₁_nHomotopic.comp_right w
  rwa [NonUnitalStarAlgHom.id_comp] at h

theorem nHomotopic_ι₁_ι₂_comp (w : D →⋆ₙₐ[ℂ] E) : NHomotopic (S.ι₁.comp w) (S.ι₂.comp w) := by
  refine ⟨fun t => (S.rot t).comp w, fun d => S.rot_continuous (w d), ?_, ?_⟩
  · show (S.rot 0).comp w = S.ι₁.comp w
    rw [S.rot_zero]
  · show (S.rot 1).comp w = S.ι₂.comp w
    rw [S.rot_one]

/-- The Cuntz sum respects homotopy in the first variable. -/
theorem sum_nHomotopic_left {x₀ x₁ : D →⋆ₙₐ[ℂ] E} (h : NHomotopic x₀ x₁)
    (x' : D →⋆ₙₐ[ℂ] E) : NHomotopic (S.sum x₀ x') (S.sum x₁ x') := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun t => S.sum (p t) x', fun d => ?_, ?_, ?_⟩
  · show Continuous fun t : ℝ => S.ι₁ (p t d) + S.ι₂ (x' d)
    exact ((continuous_nonUnitalStarAlgHom S.ι₁).comp (hp d)).add continuous_const
  · show S.sum (p 0) x' = S.sum x₀ x'
    rw [h0]
  · show S.sum (p 1) x' = S.sum x₁ x'
    rw [h1]

/-- The Cuntz sum respects homotopy in the second variable. -/
theorem sum_nHomotopic_right (x : D →⋆ₙₐ[ℂ] E) {x₀ x₁ : D →⋆ₙₐ[ℂ] E}
    (h : NHomotopic x₀ x₁) : NHomotopic (S.sum x x₀) (S.sum x x₁) := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun t => S.sum x (p t), fun d => ?_, ?_, ?_⟩
  · show Continuous fun t : ℝ => S.ι₁ (x d) + S.ι₂ (p t d)
    exact continuous_const.add ((continuous_nonUnitalStarAlgHom S.ι₂).comp (hp d))
  · show S.sum x (p 0) = S.sum x x₀
    rw [h0]
  · show S.sum x (p 1) = S.sum x x₁
    rw [h1]

end CuntzStable

end

end GroupApproximation.Full.TWWKK
