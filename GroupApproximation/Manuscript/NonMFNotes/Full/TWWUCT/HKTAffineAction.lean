import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HaagerupProper

/-!
# Affine isometric actions on real Hilbert spaces

Lane TWWUCT-C (work order WO-TWWUCT-C).  The Higson--Kasparov--Trout algebra `A(H)`
(Higson--Kasparov--Trout, *A Bott periodicity theorem for infinite dimensional Euclidean
space*, Adv. Math. 135 (1998), §4; Higson--Kasparov, Invent. Math. 144 (2001), §3) carries an
action of every group acting on `H` by affine isometries.  The action is proper when the
cocycle is metrically proper, which is the Haagerup property.  `non_mf_group_notes.tex`
(L1376--1378) needs this for amenable groups, through the UCT for `C⋆_r(G)`.

This file sets up the geometric side.

* `AffineIsometricAction G H`: an orthogonal representation `π` together with a 1-cocycle `b`,
  acting by `g • ξ = π_g ξ + b_g`.
* `AffineIsometricAction.IsMetricallyProper`: `{g | ‖b_g‖ ≤ R}` is finite for every `R`.
* `finite_bounded_return`: for a metrically proper action, only finitely many `g` move a
  point of the ball of radius `R` into that ball.
* `exists_isMetricallyProper_of_isAmenable`: a countable amenable group has a metrically
  proper affine isometric action on `CocycleSpace G`, from `exists_proper_cocycle`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe u v

/-- An affine isometric action of a group `G` on a real Hilbert space `H`: an orthogonal
representation `linearPart` and a 1-cocycle `cocycle` for it.  The action is
`g • ξ = linearPart g ξ + cocycle g` (HKT 1998, §4; HK 2001, §3). -/
structure AffineIsometricAction (G : Type u) [Group G] (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The orthogonal representation. -/
  linearPart : G → H ≃ₗᵢ[ℝ] H
  /-- The cocycle. -/
  cocycle : G → H
  linearPart_one : ∀ ξ : H, linearPart 1 ξ = ξ
  linearPart_mul : ∀ (g h : G) (ξ : H), linearPart (g * h) ξ = linearPart g (linearPart h ξ)
  cocycle_mul : ∀ g h : G, cocycle (g * h) = cocycle g + linearPart g (cocycle h)

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (b : AffineIsometricAction G H)

/-- The affine map `ξ ↦ π_g ξ + b_g`. -/
def act (g : G) (ξ : H) : H :=
  b.linearPart g ξ + b.cocycle g

theorem act_apply (g : G) (ξ : H) : b.act g ξ = b.linearPart g ξ + b.cocycle g :=
  rfl

theorem cocycle_one : b.cocycle 1 = 0 := by
  have h := b.cocycle_mul 1 1
  rw [one_mul, b.linearPart_one] at h
  have h' : b.cocycle 1 + b.cocycle 1 = b.cocycle 1 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h'

theorem act_one (ξ : H) : b.act 1 ξ = ξ := by
  rw [act_apply, b.linearPart_one, b.cocycle_one, add_zero]

theorem act_mul (g h : G) (ξ : H) : b.act (g * h) ξ = b.act g (b.act h ξ) := by
  rw [act_apply, act_apply, act_apply, b.linearPart_mul, b.cocycle_mul, map_add]
  abel

theorem act_inv_act (g : G) (ξ : H) : b.act g⁻¹ (b.act g ξ) = ξ := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : G) (ξ : H) : b.act g (b.act g⁻¹ ξ) = ξ := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem dist_act (g : G) (ξ η : H) : dist (b.act g ξ) (b.act g η) = dist ξ η := by
  rw [act_apply, act_apply, dist_add_right, LinearIsometryEquiv.dist_map]

theorem isometry_act (g : G) : Isometry (b.act g) :=
  Isometry.of_dist_eq fun ξ η => b.dist_act g ξ η

theorem continuous_act (g : G) : Continuous (b.act g) :=
  (b.isometry_act g).continuous

/-- The affine isometries `b.act g`, bundled as an equivalence of `H`. -/
def actEquiv (g : G) : H ≃ H where
  toFun := b.act g
  invFun := b.act g⁻¹
  left_inv ξ := b.act_inv_act g ξ
  right_inv ξ := b.act_act_inv g ξ

theorem cocycle_eq_act_sub (g : G) (ξ : H) : b.cocycle g = b.act g ξ - b.linearPart g ξ := by
  rw [act_apply, add_sub_cancel_left]

/-- Metric properness of the cocycle (Haagerup property, HK 2001 §3): every set
`{g | ‖b_g‖ ≤ R}` is finite. -/
def IsMetricallyProper : Prop :=
  ∀ R : ℝ, {g : G | ‖b.cocycle g‖ ≤ R}.Finite

/-- The norm of the cocycle bounds how far a point of the `R`-ball can move. -/
theorem norm_cocycle_le_of_mem_ball {g : G} {ξ : H} {R : ℝ} (hξ : ‖ξ‖ ≤ R)
    (hgξ : ‖b.act g ξ‖ ≤ R) : ‖b.cocycle g‖ ≤ R + R := by
  rw [b.cocycle_eq_act_sub g ξ]
  calc ‖b.act g ξ - b.linearPart g ξ‖ ≤ ‖b.act g ξ‖ + ‖b.linearPart g ξ‖ := norm_sub_le _ _
    _ = ‖b.act g ξ‖ + ‖ξ‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ R + R := add_le_add hgξ hξ

/-- For a metrically proper action only finitely many group elements bring a point of the
closed `R`-ball back into that ball. -/
theorem finite_bounded_return (hb : b.IsMetricallyProper) (R : ℝ) :
    {g : G | ∃ ξ : H, ‖ξ‖ ≤ R ∧ ‖b.act g ξ‖ ≤ R}.Finite := by
  refine (hb (R + R)).subset ?_
  rintro g ⟨ξ, hξ, hgξ⟩
  exact b.norm_cocycle_le_of_mem_ball hξ hgξ

end AffineIsometricAction

section Haagerup

variable {G : Type u} [Group G]

/-- The affine isometric action on `CocycleSpace G = ℓ²(ℕ × G, ℝ)` given by the translation
representation and a translation cocycle. -/
def translationAffineAction (b : G → CocycleSpace G)
    (hb : ∀ g h : G, b (g * h) = b g + translation g (b h)) :
    AffineIsometricAction G (CocycleSpace G) where
  linearPart := translation
  cocycle := b
  linearPart_one := translation_one
  linearPart_mul := translation_mul
  cocycle_mul := hb

/-- **Haagerup property for amenable groups** (Bekka--Chérix--Valette), packaged as an affine
isometric action: a countable amenable group admits a metrically proper affine isometric
action on a separable real Hilbert space.  Input to HKT 1998 §4 / HK 2001 Thm 1.1. -/
theorem exists_isMetricallyProper_of_isAmenable [Countable G]
    (hG : Amenability.IsAmenable G) :
    ∃ b : AffineIsometricAction G (CocycleSpace G), b.IsMetricallyProper := by
  obtain ⟨c, hc, hproper⟩ := exists_proper_cocycle hG
  exact ⟨translationAffineAction c hc, hproper⟩

end Haagerup

end

end GroupApproximation.Full.TWWUCT
