import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Kirchberg.RealDilation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Kirchberg.TensorSquare

/-!
# The frame vector of Kirchberg's argument (lane A2Kirchberg)

For Kirchberg, Math. Ann. 299 (1994), Theorem 1.1 (property (T) and the factorization
property imply residual finiteness), the Kirchberg--Thom step of table row A2 of
`simple_kazhdan_sofic_group.tex` (l.54--59; bibitem l.864--866).

Let `X : G → M_Y(ℂ)` be positive definite with `X(1) = 1`, let `σ` be its real dilation
on `K`, and let `f_a = V(β a)` be the images of the real basis `β` of `ℂ^Y`.  They are
orthonormal, so

  `η = (2k)^{-1/2} ∑ₐ f_a ⊗ f_a ∈ K ⊗̂ K`,   `k = |Y|`,

is a unit vector with

* `⟪(σ ⊗ σ)(g) η, η⟫ = ∑ₓ ∑ᵧ |X(g)ₓᵧ|² / k = Re tr (X(g)ᴴ X(g)) / k`, the Gram estimate;
* `⟪η, ∑ₐ σ(h) f_a ⊗ f_a⟫ / √(2k) = Re tr X(h) / k`, the trace estimate.
-/

namespace GroupApproximation.Full.A2Kirchberg.Frame

open Matrix

universe u

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The normalizing constant `(2k)^{-1/2}`. -/
noncomputable def kScale (Y : Type) [Fintype Y] : ℝ :=
  (Real.sqrt (2 * (Fintype.card Y : ℝ)))⁻¹

theorem kScale_mul_kScale (Y : Type) [Fintype Y] :
    kScale Y * kScale Y = (2 * (Fintype.card Y : ℝ))⁻¹ := by
  rw [kScale, ← mul_inv,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card Y : ℝ))]

/-- A unit vector close to an other one pairs with it above `3/4`. -/
theorem inner_gt_of_near {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ζ η : E} (hη : ‖η‖ = 1) (hn : ‖η - ζ‖ < 1 / 4) : 3 / 4 < ⟪ζ, η⟫ := by
  have h1 : ⟪ζ, η⟫ = ⟪η, η⟫ - ⟪η - ζ, η⟫ := by
    rw [inner_sub_left]
    ring
  have h2 : ⟪η, η⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hη, one_pow]
  have h3 : ⟪η - ζ, η⟫ ≤ ‖η - ζ‖ * ‖η‖ := real_inner_le_norm _ _
  rw [hη, mul_one] at h3
  linarith

/-- A vector close to `η` pairs with a unit vector `w` below `⟪η, w⟫ + 1/4`. -/
theorem inner_lt_of_near {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ζ η w : E} (hw : ‖w‖ = 1) (hn : ‖η - ζ‖ < 1 / 4) (hηw : ⟪η, w⟫ < 1 / 4) :
    ⟪ζ, w⟫ < 1 / 2 := by
  have h1 : ⟪ζ, w⟫ = ⟪η, w⟫ - ⟪η - ζ, w⟫ := by
    rw [inner_sub_left]
    ring
  have h2 : |⟪η - ζ, w⟫| ≤ ‖η - ζ‖ * ‖w‖ := abs_real_inner_le_norm _ _
  have h3 := neg_abs_le ⟪η - ζ, w⟫
  rw [hw, mul_one] at h2
  linarith

variable {G : Type u} [Group G] {Y : Type} [Fintype Y] [DecidableEq Y]
variable (X : G → Matrix Y Y ℂ) (hX : RealDilation.IsPositiveDefinite X)

theorem sum_sum_ite_one :
    ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y, (if a = b then (1 : ℝ) else 0) = 2 * (Fintype.card Y : ℝ) := by
  calc ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y, (if a = b then (1 : ℝ) else 0)
      = ∑ _a : Y ⊕ Y, (1 : ℝ) :=
        Finset.sum_congr rfl fun a _ ↦ Fintype.sum_ite_eq a (fun _ ↦ (1 : ℝ))
    _ = 2 * (Fintype.card Y : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, nsmul_eq_mul, mul_one,
          Nat.cast_add]
        ring

/-- The frame vectors `f_a = V(β a)` of the dilation. -/
noncomputable def kFrame (a : Y ⊕ Y) : RealDilation.Space X hX :=
  RealDilation.vec X hX (RealForms.realBasis a)

theorem inner_kFrame_kFrame (hone : X 1 = 1) (a b : Y ⊕ Y) :
    ⟪kFrame X hX a, kFrame X hX b⟫ = if a = b then 1 else 0 := by
  have h := RealDilation.inner_vec_vec X hX (RealForms.realBasis a) (RealForms.realBasis b)
  rw [hone, RealForms.re_pairing_one] at h
  exact h

theorem inner_kFrame_rep (g : G) (a b : Y ⊕ Y) :
    ⟪kFrame X hX a, RealDilation.rep X hX g (kFrame X hX b)⟫
      = (RealForms.pairing (X g) (RealForms.realBasis a) (RealForms.realBasis b)).re :=
  RealDilation.inner_vec_rep_vec X hX _ _ g

/-- **The frame vector** `η = (2k)^{-1/2} ∑ₐ f_a ⊗ f_a`. -/
noncomputable def kEta : TensorSq.TensorSquare (RealDilation.Space X hX) :=
  kScale Y • ∑ a : Y ⊕ Y, TensorSq.tmulC (kFrame X hX a) (kFrame X hX a)

/-- The frame vector moved on the first leg, `(2k)^{-1/2} ∑ₐ A f_a ⊗ f_a`. -/
noncomputable def kEtaMoved (A : RealDilation.Space X hX ≃ₗᵢ[ℝ] RealDilation.Space X hX) :
    TensorSq.TensorSquare (RealDilation.Space X hX) :=
  kScale Y • ∑ a : Y ⊕ Y, TensorSq.tmulC (A (kFrame X hX a)) (kFrame X hX a)

theorem inner_kEta_kEta (hone : X 1 = 1) (hk : 0 < Fintype.card Y) :
    ⟪kEta X hX, kEta X hX⟫ = 1 := by
  have hk' : (0 : ℝ) < 2 * (Fintype.card Y : ℝ) := mul_pos two_pos (Nat.cast_pos.mpr hk)
  have hsum : ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y,
      ⟪kFrame X hX a, kFrame X hX b⟫ * ⟪kFrame X hX a, kFrame X hX b⟫
        = 2 * (Fintype.card Y : ℝ) := by
    rw [← sum_sum_ite_one (Y := Y)]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    rw [inner_kFrame_kFrame X hX hone]
    by_cases h : a = b
    · rw [if_pos h, one_mul]
    · rw [if_neg h, zero_mul]
  rw [kEta, real_inner_smul_left, real_inner_smul_right, TensorSq.inner_sum_tmulC, hsum,
    ← mul_assoc, kScale_mul_kScale]
  exact inv_mul_cancel₀ hk'.ne'

theorem inner_kEtaMoved_self (hone : X 1 = 1) (hk : 0 < Fintype.card Y)
    (A : RealDilation.Space X hX ≃ₗᵢ[ℝ] RealDilation.Space X hX) :
    ⟪kEtaMoved X hX A, kEtaMoved X hX A⟫ = 1 := by
  have hk' : (0 : ℝ) < 2 * (Fintype.card Y : ℝ) := mul_pos two_pos (Nat.cast_pos.mpr hk)
  have hsum : ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y,
      ⟪A (kFrame X hX a), A (kFrame X hX b)⟫ * ⟪kFrame X hX a, kFrame X hX b⟫
        = 2 * (Fintype.card Y : ℝ) := by
    rw [← sum_sum_ite_one (Y := Y)]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    rw [LinearIsometryEquiv.inner_map_map, inner_kFrame_kFrame X hX hone]
    by_cases h : a = b
    · rw [if_pos h, one_mul]
    · rw [if_neg h, zero_mul]
  rw [kEtaMoved, real_inner_smul_left, real_inner_smul_right, TensorSq.inner_sum_tmulC, hsum,
    ← mul_assoc, kScale_mul_kScale]
  exact inv_mul_cancel₀ hk'.ne'

/-- **The Gram identity** `⟪(σ ⊗ σ)(g) η, η⟫ = ∑ₓ ∑ᵧ |X(g)ₓᵧ|² / k`. -/
theorem inner_diag_kEta_kEta (g : G) :
    ⟪TensorSq.diag (RealDilation.rep X hX) g (kEta X hX), kEta X hX⟫
      = (∑ x : Y, ∑ y : Y, ‖X g x y‖ ^ 2) / (Fintype.card Y : ℝ) := by
  have hsum : ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y,
      ⟪RealDilation.rep X hX g (kFrame X hX a), kFrame X hX b⟫
        * ⟪RealDilation.rep X hX g (kFrame X hX a), kFrame X hX b⟫
        = 2 * ∑ x : Y, ∑ y : Y, ‖X g x y‖ ^ 2 := by
    calc ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y,
          ⟪RealDilation.rep X hX g (kFrame X hX a), kFrame X hX b⟫
            * ⟪RealDilation.rep X hX g (kFrame X hX a), kFrame X hX b⟫
        = ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y,
            ((RealForms.pairing (X g) (RealForms.realBasis b) (RealForms.realBasis a)).re) ^ 2 :=
          Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by
            rw [real_inner_comm, inner_kFrame_rep X hX g b a, sq]
      _ = ∑ b : Y ⊕ Y, ∑ a : Y ⊕ Y,
            ((RealForms.pairing (X g) (RealForms.realBasis b) (RealForms.realBasis a)).re) ^ 2 :=
          Finset.sum_comm
      _ = 2 * ∑ x : Y, ∑ y : Y, ‖X g x y‖ ^ 2 := RealForms.sum_sq_re_pairing (X g)
  have hd : ∑ a : Y ⊕ Y, TensorSq.diag (RealDilation.rep X hX) g
      (TensorSq.tmulC (kFrame X hX a) (kFrame X hX a))
        = ∑ a : Y ⊕ Y, TensorSq.tmulC (RealDilation.rep X hX g (kFrame X hX a))
            (RealDilation.rep X hX g (kFrame X hX a)) :=
    Finset.sum_congr rfl fun a _ ↦ TensorSq.diag_tmulC _ g _ _
  rw [kEta, LinearIsometryEquiv.map_smul, map_sum, hd, real_inner_smul_left,
    real_inner_smul_right, TensorSq.inner_sum_tmulC, hsum, ← mul_assoc, kScale_mul_kScale]
  ring

/-- Pairing the frame vector with a moved frame vector. -/
theorem inner_kEta_kEtaMoved (hone : X 1 = 1)
    (A : RealDilation.Space X hX ≃ₗᵢ[ℝ] RealDilation.Space X hX) :
    ⟪kEta X hX, kEtaMoved X hX A⟫
      = (∑ a : Y ⊕ Y, ⟪kFrame X hX a, A (kFrame X hX a)⟫) / (2 * (Fintype.card Y : ℝ)) := by
  have hsum : ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y,
      ⟪kFrame X hX a, A (kFrame X hX b)⟫ * ⟪kFrame X hX a, kFrame X hX b⟫
        = ∑ a : Y ⊕ Y, ⟪kFrame X hX a, A (kFrame X hX a)⟫ := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_eq_single a]
    · rw [inner_kFrame_kFrame X hX hone, if_pos (rfl : a = a), mul_one]
    · intro b _ hb
      rw [inner_kFrame_kFrame X hX hone, if_neg (Ne.symm hb), mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [kEta, kEtaMoved, real_inner_smul_left, real_inner_smul_right, TensorSq.inner_sum_tmulC,
    hsum, ← mul_assoc, kScale_mul_kScale, div_eq_inv_mul]

/-- **The trace identity** `⟪η, (2k)^{-1/2} ∑ₐ σ(h) f_a ⊗ f_a⟫ = Re tr X(h) / k`. -/
theorem inner_kEta_kEtaMoved_rep (hone : X 1 = 1) (h : G) :
    ⟪kEta X hX, kEtaMoved X hX (RealDilation.rep X hX h)⟫
      = (Matrix.trace (X h)).re / (Fintype.card Y : ℝ) := by
  have hsum : ∑ a : Y ⊕ Y, ⟪kFrame X hX a, RealDilation.rep X hX h (kFrame X hX a)⟫
      = 2 * (Matrix.trace (X h)).re := by
    rw [← RealForms.sum_re_pairing_diag (X h)]
    exact Finset.sum_congr rfl fun a _ ↦ inner_kFrame_rep X hX h a a
  rw [inner_kEta_kEtaMoved X hX hone, hsum,
    mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)]

theorem norm_kEta (hone : X 1 = 1) (hk : 0 < Fintype.card Y) : ‖kEta X hX‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, inner_kEta_kEta X hX hone hk, Real.sqrt_one]

theorem norm_kEtaMoved (hone : X 1 = 1) (hk : 0 < Fintype.card Y)
    (A : RealDilation.Space X hX ≃ₗᵢ[ℝ] RealDilation.Space X hX) :
    ‖kEtaMoved X hX A‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, inner_kEtaMoved_self X hX hone hk A, Real.sqrt_one]

/-- **The frame vector is almost invariant** when the Gram estimate holds. -/
theorem norm_diag_kEta_sub_lt (hone : X 1 = 1) (hk : 0 < Fintype.card Y) {c : ℝ} (hc : 0 < c)
    (g : G) (hg : 1 - c ^ 2 / 2 < (∑ x : Y, ∑ y : Y, ‖X g x y‖ ^ 2) / (Fintype.card Y : ℝ)) :
    ‖TensorSq.diag (RealDilation.rep X hX) g (kEta X hX) - kEta X hX‖ < c := by
  have h2 : ‖TensorSq.diag (RealDilation.rep X hX) g (kEta X hX) - kEta X hX‖ ^ 2 < c ^ 2 := by
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map, norm_kEta X hX hone hk,
      inner_diag_kEta_kEta X hX g]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hc.le h2

/-- If `ζ` does not see `A` on the first leg, it pairs equally with `η` and the moved `η`. -/
theorem inner_kEtaMoved_eq (A : RealDilation.Space X hX ≃ₗᵢ[ℝ] RealDilation.Space X hX)
    (ζ : TensorSq.TensorSquare (RealDilation.Space X hX))
    (hid : ∀ x y : RealDilation.Space X hX,
      ⟪ζ, TensorSq.tmulC (A x) y⟫ = ⟪ζ, TensorSq.tmulC x y⟫) :
    ⟪ζ, kEtaMoved X hX A⟫ = ⟪ζ, kEta X hX⟫ := by
  rw [kEtaMoved, kEta, real_inner_smul_right, real_inner_smul_right, inner_sum, inner_sum]
  exact congrArg (fun t : ℝ ↦ kScale Y * t) (Finset.sum_congr rfl fun a _ ↦ hid _ _)

end GroupApproximation.Full.A2Kirchberg.Frame
