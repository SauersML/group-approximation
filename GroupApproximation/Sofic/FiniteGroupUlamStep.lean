import GroupApproximation.Sofic.FinitePacketCovariance

/-!
# One dimension-free Ulam correction step for a finite group

This is the first constructive layer of finite-group corona tail
exactification.  It uses only finite averaging and the in-repository polar
functional calculus.  No semiprojectivity or external stability theorem is
assumed.

For a unitary table `φ : F → U(A)`, put

`T_g = |F|⁻¹ ∑ₓ φ(gx) φ(x)⋆`.

If the multiplication table has defect at most `δ`, then `T_g` is within
`δ` of `φ(g)`.  For `δ ≤ 1/8`, polar correction therefore gives another
unitary table within `6δ` of the old one.  The subsequent iteration module
will prove that this correction reduces the defect quadratically.
-/

namespace GroupApproximation
namespace FiniteGroupUlamStep

open PolarLiftingGeneralCStar FinitePacketCovariance

noncomputable section

universe u v

variable {F : Type u} [Group F] [Fintype F]
variable {A : Type v} [CStarAlgebra A]

/-- Uniform operator-norm multiplication-table control. -/
def MultiplicativeDefectAtMost (φ : F → unitary A) (δ : ℝ) : Prop :=
  ∀ g h : F,
    ‖((φ (g * h) : unitary A) : A) -
      ((φ g : unitary A) : A) * ((φ h : unitary A) : A)‖ ≤ δ

/-- The signed multiplication error. -/
def multiplicationError (φ : F → unitary A) (g h : F) : A :=
  ((φ (g * h) : unitary A) : A) -
    ((φ g : unitary A) : A) * ((φ h : unitary A) : A)

omit [Fintype F] in
/-- The multiplication error satisfies an exact algebraic cocycle identity.
This is the cancellation responsible for quadratic improvement. -/
theorem multiplicationError_cocycle (φ : F → unitary A) (g h x : F) :
    multiplicationError φ (g * h) x =
      multiplicationError φ g (h * x) +
        ((φ g : unitary A) : A) * multiplicationError φ h x -
          multiplicationError φ g h * ((φ x : unitary A) : A) := by
  unfold multiplicationError
  rw [mul_assoc]
  noncomm_ring

/-- The averaged first-order error in the Reynolds correction. -/
noncomputable def averagedError (φ : F → unitary A) (g : F) : A :=
  ((Fintype.card F : ℂ)⁻¹) •
    ∑ x : F, multiplicationError φ g x * star ((φ x : unitary A) : A)

/-- The genuinely quadratic remainder in the averaged-error cocycle. -/
noncomputable def quadraticRemainder (φ : F → unitary A) (g h : F) : A :=
  ((Fintype.card F : ℂ)⁻¹) •
    ∑ x : F, multiplicationError φ g (h * x) *
      (star ((φ x : unitary A) : A) -
        star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A))

omit [Fintype F] in
/-- The second factor in `quadraticRemainder` is another copy of the
multiplication error, transported by a unitary. -/
theorem norm_star_sub_star_mul_le
    (φ : F → unitary A) {δ : ℝ}
    (hφ : MultiplicativeDefectAtMost φ δ) (h x : F) :
    ‖star ((φ x : unitary A) : A) -
        star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A)‖ ≤ δ := by
  have hid : star ((φ x : unitary A) : A) -
        star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A) =
      -(star (multiplicationError φ h x) * ((φ h : unitary A) : A)) := by
    unfold multiplicationError
    rw [star_sub, star_mul]
    have hh : star ((φ h : unitary A) : A) * ((φ h : unitary A) : A) = 1 :=
      Unitary.star_mul_self_of_mem (φ h).prop
    rw [sub_mul, mul_assoc, hh, mul_one]
    module
  rw [hid, norm_neg,
    CStarRing.norm_mul_mem_unitary _ (φ h).prop, norm_star]
  exact hφ h x

/-- The remainder left by Reynolds averaging has quadratic norm. -/
theorem norm_quadraticRemainder_le
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hφ : MultiplicativeDefectAtMost φ δ) (g h : F) :
    ‖quadraticRemainder φ g h‖ ≤ δ ^ 2 := by
  classical
  unfold quadraticRemainder
  rw [norm_smul]
  calc
    ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ‖∑ x : F, multiplicationError φ g (h * x) *
            (star ((φ x : unitary A) : A) -
              star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A))‖ ≤
        ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ∑ x : F, ‖multiplicationError φ g (h * x) *
            (star ((φ x : unitary A) : A) -
              star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖((Fintype.card F : ℂ)⁻¹)‖ * ∑ _x : F, δ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro x _
      calc
        ‖multiplicationError φ g (h * x) *
            (star ((φ x : unitary A) : A) -
              star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A))‖ ≤
            ‖multiplicationError φ g (h * x)‖ *
              ‖star ((φ x : unitary A) : A) -
                star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A)‖ :=
          norm_mul_le _ _
        _ ≤ δ * δ := mul_le_mul (hφ g (h * x))
          (norm_star_sub_star_mul_le φ hφ h x) (norm_nonneg _) hδ0
        _ = δ ^ 2 := by ring
    _ = δ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [norm_inv, Complex.norm_natCast, smul_eq_mul]
      have hc : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- Averaging turns the exact multiplication-error cocycle into a cocycle up
to the explicitly quadratic remainder. -/
theorem averagedError_mul (φ : F → unitary A) (g h : F) :
    averagedError φ (g * h) =
      averagedError φ g * ((φ h : unitary A) : A) +
        ((φ g : unitary A) : A) * averagedError φ h -
          multiplicationError φ g h + quadraticRemainder φ g h := by
  classical
  let c : ℂ := (Fintype.card F : ℂ)⁻¹
  let Eg : F → A := fun x ↦ multiplicationError φ g x
  let Eh : F → A := fun x ↦ multiplicationError φ h x
  let Q : A := ∑ x : F, Eg (h * x) *
    (star ((φ x : unitary A) : A) -
      star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A))
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hreindex :
      (∑ x : F, Eg (h * x) * star ((φ (h * x) : unitary A) : A)) =
        ∑ x : F, Eg x * star ((φ x : unitary A) : A) := by
    exact Fintype.sum_equiv (Equiv.mulLeft h)
      (fun x : F ↦ Eg (h * x) * star ((φ (h * x) : unitary A) : A))
      (fun x : F ↦ Eg x * star ((φ x : unitary A) : A)) (fun _ ↦ rfl)
  have hfirst :
      (∑ x : F, Eg (h * x) * star ((φ x : unitary A) : A)) =
        (∑ x : F, Eg x * star ((φ x : unitary A) : A)) *
            ((φ h : unitary A) : A) + Q := by
    dsimp [Q]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hassoc :
        (∑ x : F, Eg (h * x) *
          (star ((φ (h * x) : unitary A) : A) * ((φ h : unitary A) : A))) =
          (∑ x : F, Eg (h * x) * star ((φ (h * x) : unitary A) : A)) *
            ((φ h : unitary A) : A) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_assoc]
    rw [hassoc, hreindex]
    noncomm_ring
  have hcocycleSum :
      (∑ x : F, multiplicationError φ (g * h) x *
          star ((φ x : unitary A) : A)) =
        (∑ x : F, Eg (h * x) * star ((φ x : unitary A) : A)) +
          ((φ g : unitary A) : A) *
            (∑ x : F, Eh x * star ((φ x : unitary A) : A)) -
              (Fintype.card F) • multiplicationError φ g h := by
    calc
      (∑ x : F, multiplicationError φ (g * h) x *
          star ((φ x : unitary A) : A)) =
          ∑ x : F, (Eg (h * x) * star ((φ x : unitary A) : A) +
            ((φ g : unitary A) : A) *
              (Eh x * star ((φ x : unitary A) : A)) -
                multiplicationError φ g h) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [multiplicationError_cocycle]
        have hx : ((φ x : unitary A) : A) * star ((φ x : unitary A) : A) = 1 :=
          Unitary.mul_star_self_of_mem (φ x).prop
        rw [sub_mul, add_mul]
        simp_rw [mul_assoc]
        rw [hx, mul_one]
      _ = (∑ x : F, Eg (h * x) * star ((φ x : unitary A) : A)) +
          ((φ g : unitary A) : A) *
            (∑ x : F, Eh x * star ((φ x : unitary A) : A)) -
              (Fintype.card F) • multiplicationError φ g h := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, Finset.card_univ]
  unfold averagedError quadraticRemainder
  change c • (∑ x : F, multiplicationError φ (g * h) x *
      star ((φ x : unitary A) : A)) =
    (c • ∑ x : F, Eg x * star ((φ x : unitary A) : A)) *
        ((φ h : unitary A) : A) +
      ((φ g : unitary A) : A) *
        (c • ∑ x : F, Eh x * star ((φ x : unitary A) : A)) -
      multiplicationError φ g h + c • Q
  rw [hcocycleSum, hfirst]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_add, smul_sub, smul_smul, smul_mul_assoc, mul_smul_comm]
  have hcCard : c * (Fintype.card F : ℂ) = 1 := by
    exact inv_mul_cancel₀ hcard
  rw [hcCard, one_smul]
  module

/-- The unitarized Reynolds correction before taking its polar part. -/
def reynoldsSummand (φ : F → unitary A) (g x : F) : A :=
  ((φ (g * x) : unitary A) : A) * star ((φ x : unitary A) : A)

omit [Fintype F] in
/-- Every Reynolds summand is unitary. -/
theorem reynoldsSummand_mem_unitary (φ : F → unitary A) (g x : F) :
    reynoldsSummand φ g x ∈ unitary A :=
  (unitary A).mul_mem (φ (g * x)).prop (Unitary.star_mem (φ x).prop)

/-- The unitarized Reynolds correction before taking its polar part. -/
noncomputable def reynoldsCorrection (φ : F → unitary A) (g : F) : A :=
  ((Fintype.card F : ℂ)⁻¹) •
    ∑ x : F, reynoldsSummand φ g x

/-- The exact left variance identity for a finite average of unitaries. -/
theorem reynoldsVariance_left (φ : F → unitary A) (g : F) :
    ((Fintype.card F : ℂ)⁻¹) •
        ∑ x : F,
          star (reynoldsSummand φ g x - reynoldsCorrection φ g) *
            (reynoldsSummand φ g x - reynoldsCorrection φ g) =
      1 - star (reynoldsCorrection φ g) * reynoldsCorrection φ g := by
  classical
  let N : ℂ := Fintype.card F
  let c : ℂ := N⁻¹
  let S : A := ∑ x : F, reynoldsSummand φ g x
  let T : A := c • S
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hcN : c * N = 1 := inv_mul_cancel₀ hN
  have hT : reynoldsCorrection φ g = T := rfl
  have hsumUnitary : (∑ x : F,
      star (reynoldsSummand φ g x) * reynoldsSummand φ g x) =
      (Fintype.card F) • (1 : A) := by
    calc
      (∑ x : F, star (reynoldsSummand φ g x) * reynoldsSummand φ g x) =
          ∑ _x : F, (1 : A) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Unitary.star_mul_self_of_mem (reynoldsSummand_mem_unitary φ g x)]
      _ = (Fintype.card F) • (1 : A) := by
        rw [Finset.sum_const, Finset.card_univ]
  have hexpand : (∑ x : F,
      star (reynoldsSummand φ g x - T) *
        (reynoldsSummand φ g x - T)) =
      (Fintype.card F) • (1 : A) - star S * T - star T * S +
        (Fintype.card F) • (star T * T) := by
    calc
      (∑ x : F, star (reynoldsSummand φ g x - T) *
          (reynoldsSummand φ g x - T)) =
          ∑ x : F, (star (reynoldsSummand φ g x) * reynoldsSummand φ g x -
            star (reynoldsSummand φ g x) * T -
            star T * reynoldsSummand φ g x + star T * T) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [star_sub]
        noncomm_ring
      _ = (∑ x : F, star (reynoldsSummand φ g x) * reynoldsSummand φ g x) -
          (∑ x : F, star (reynoldsSummand φ g x) * T) -
          (∑ x : F, star T * reynoldsSummand φ g x) +
          ∑ _x : F, star T * T := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib]
      _ = (Fintype.card F) • (1 : A) - star S * T - star T * S +
          (Fintype.card F) • (star T * T) := by
        rw [hsumUnitary, ← Finset.sum_mul, ← Finset.mul_sum,
          Finset.sum_const]
        simp [S]
  have hST : S = N • T := by
    dsimp [T]
    rw [smul_smul]
    simp only [N, c]
    rw [mul_inv_cancel₀ hN, one_smul]
  rw [hT]
  change c • (∑ x : F, star (reynoldsSummand φ g x - T) *
      (reynoldsSummand φ g x - T)) = 1 - star T * T
  rw [hexpand]
  rw [hST]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [star_smul]
  change c • (N • (1 : A) - star N • star T * T - star T * N • T +
      N • (star T * T)) = 1 - star T * T
  have hstarN : star N = N := by simp [N]
  rw [hstarN]
  simp only [smul_sub, smul_add, smul_smul, smul_mul_assoc, mul_smul_comm]
  rw [hcN]
  simp only [one_smul]
  module

/-- The Reynolds correction is the old table plus its averaged error. -/
theorem reynoldsCorrection_eq_add_averagedError
    (φ : F → unitary A) (g : F) :
    reynoldsCorrection φ g = ((φ g : unitary A) : A) + averagedError φ g := by
  classical
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hsplit : (∑ x : F,
      ((((φ (g * x) : unitary A) : A) -
          ((φ g : unitary A) : A) * ((φ x : unitary A) : A)) *
            star ((φ x : unitary A) : A))) =
      (∑ x : F, ((φ (g * x) : unitary A) : A) *
          star ((φ x : unitary A) : A)) -
        ∑ x : F, (((φ g : unitary A) : A) * ((φ x : unitary A) : A)) *
          star ((φ x : unitary A) : A) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  unfold reynoldsCorrection averagedError multiplicationError
  rw [hsplit, smul_sub]
  have hterm : (∑ x : F,
      (((φ g : unitary A) : A) * ((φ x : unitary A) : A)) *
        star ((φ x : unitary A) : A)) =
      ∑ _x : F, ((φ g : unitary A) : A) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_assoc, Unitary.mul_star_self_of_mem (φ x).prop, mul_one]
  rw [hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ hcard, one_smul]
  abel

/-- The Reynolds multiplication defect is exactly a product of averaged
errors minus the quadratic remainder. -/
theorem reynoldsCorrection_mul_sub (φ : F → unitary A) (g h : F) :
    reynoldsCorrection φ g * reynoldsCorrection φ h -
        reynoldsCorrection φ (g * h) =
      averagedError φ g * averagedError φ h - quadraticRemainder φ g h := by
  rw [reynoldsCorrection_eq_add_averagedError,
    reynoldsCorrection_eq_add_averagedError,
    reynoldsCorrection_eq_add_averagedError,
    averagedError_mul]
  unfold multiplicationError
  noncomm_ring

/-- The averaged error has norm at most the table defect. -/
theorem norm_averagedError_le
    (φ : F → unitary A) {δ : ℝ}
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    ‖averagedError φ g‖ ≤ δ := by
  classical
  unfold averagedError
  rw [norm_smul]
  calc
    ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ‖∑ x : F, multiplicationError φ g x *
            star ((φ x : unitary A) : A)‖ ≤
        ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ∑ x : F, ‖multiplicationError φ g x *
            star ((φ x : unitary A) : A)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ∑ x : F, ‖multiplicationError φ g x‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (φ x).prop)]
    _ ≤ ‖((Fintype.card F : ℂ)⁻¹)‖ * ∑ _x : F, δ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum fun x _ ↦ hφ g x
    _ = δ := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [norm_inv, Complex.norm_natCast, smul_eq_mul]
      have hc : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- The raw Reynolds average has quadratic multiplication defect. -/
theorem norm_reynoldsCorrection_mul_sub_le
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hφ : MultiplicativeDefectAtMost φ δ) (g h : F) :
    ‖reynoldsCorrection φ g * reynoldsCorrection φ h -
        reynoldsCorrection φ (g * h)‖ ≤ 2 * δ ^ 2 := by
  rw [reynoldsCorrection_mul_sub]
  calc
    ‖averagedError φ g * averagedError φ h - quadraticRemainder φ g h‖ ≤
        ‖averagedError φ g * averagedError φ h‖ +
          ‖quadraticRemainder φ g h‖ := norm_sub_le _ _
    _ ≤ ‖averagedError φ g‖ * ‖averagedError φ h‖ +
          ‖quadraticRemainder φ g h‖ :=
      add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ δ * δ + δ ^ 2 := add_le_add
      (mul_le_mul (norm_averagedError_le φ hφ g)
        (norm_averagedError_le φ hφ h) (norm_nonneg _) hδ0)
      (norm_quadraticRemainder_le φ hδ0 hφ g h)
    _ = 2 * δ ^ 2 := by ring

omit [Fintype F] in
/-- Every Reynolds summand is as close to `φ(g)` as the corresponding
multiplication-table entry. -/
theorem norm_reynoldsSummand_sub_le
    (φ : F → unitary A) {δ : ℝ}
    (hφ : MultiplicativeDefectAtMost φ δ) (g x : F) :
    ‖((φ (g * x) : unitary A) : A) * star ((φ x : unitary A) : A) -
        ((φ g : unitary A) : A)‖ ≤ δ := by
  have hunit : ((φ x : unitary A) : A) * star ((φ x : unitary A) : A) = 1 :=
    Unitary.mul_star_self_of_mem (φ x).prop
  have hid : ((φ (g * x) : unitary A) : A) *
        star ((φ x : unitary A) : A) - ((φ g : unitary A) : A) =
      (((φ (g * x) : unitary A) : A) -
        ((φ g : unitary A) : A) * ((φ x : unitary A) : A)) *
          star ((φ x : unitary A) : A) := by
    rw [sub_mul, mul_assoc, hunit, mul_one]
  rw [hid, CStarRing.norm_mul_mem_unitary _
    (Unitary.star_mem (φ x).prop)]
  exact hφ g x

/-- The Reynolds correction is within the original table defect of `φ(g)`. -/
theorem norm_reynoldsCorrection_sub_le
    (φ : F → unitary A) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    ‖reynoldsCorrection φ g - ((φ g : unitary A) : A)‖ ≤ δ := by
  classical
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hrewrite : reynoldsCorrection φ g - ((φ g : unitary A) : A) =
      ((Fintype.card F : ℂ)⁻¹) •
        ∑ x : F, (((φ (g * x) : unitary A) : A) *
          star ((φ x : unitary A) : A) - ((φ g : unitary A) : A)) := by
    unfold reynoldsCorrection reynoldsSummand
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_sub]
    rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hrewrite, norm_smul]
  calc
    ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ‖∑ x : F, (((φ (g * x) : unitary A) : A) *
            star ((φ x : unitary A) : A) - ((φ g : unitary A) : A))‖
        ≤ ‖((Fintype.card F : ℂ)⁻¹)‖ *
            ∑ x : F, ‖((φ (g * x) : unitary A) : A) *
              star ((φ x : unitary A) : A) - ((φ g : unitary A) : A)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖((Fintype.card F : ℂ)⁻¹)‖ * ∑ _x : F, δ :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x _ ↦ norm_reynoldsSummand_sub_le φ hφ g x)
        (norm_nonneg _)
    _ = δ := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [norm_inv, Complex.norm_natCast, smul_eq_mul]
      have hc : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- A Reynolds summand differs from its average by at most twice the original
table defect. -/
theorem norm_reynoldsSummand_sub_correction_le
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hφ : MultiplicativeDefectAtMost φ δ) (g x : F) :
    ‖reynoldsSummand φ g x - reynoldsCorrection φ g‖ ≤ 2 * δ := by
  have hsplit : reynoldsSummand φ g x - reynoldsCorrection φ g =
      (reynoldsSummand φ g x - ((φ g : unitary A) : A)) +
        (((φ g : unitary A) : A) - reynoldsCorrection φ g) := by
    abel
  rw [hsplit]
  calc
    ‖(reynoldsSummand φ g x - ((φ g : unitary A) : A)) +
        (((φ g : unitary A) : A) - reynoldsCorrection φ g)‖ ≤
        ‖reynoldsSummand φ g x - ((φ g : unitary A) : A)‖ +
          ‖((φ g : unitary A) : A) - reynoldsCorrection φ g‖ := norm_add_le _ _
    _ ≤ δ + δ := add_le_add
      (norm_reynoldsSummand_sub_le φ hφ g x) (by
        rw [← norm_neg, neg_sub]
        exact norm_reynoldsCorrection_sub_le φ hδ0 hφ g)
    _ = 2 * δ := by ring

/-- A finite average of unitary Reynolds summands is contractive. -/
theorem norm_reynoldsCorrection_le_one [Nontrivial A]
    (φ : F → unitary A) (g : F) :
    ‖reynoldsCorrection φ g‖ ≤ 1 := by
  classical
  unfold reynoldsCorrection
  rw [norm_smul]
  calc
    ‖((Fintype.card F : ℂ)⁻¹)‖ * ‖∑ x : F, reynoldsSummand φ g x‖ ≤
        ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ∑ x : F, ‖reynoldsSummand φ g x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖((Fintype.card F : ℂ)⁻¹)‖ * ∑ _x : F, (1 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [CStarRing.norm_of_mem_unitary (reynoldsSummand_mem_unitary φ g x)]
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [norm_inv, Complex.norm_natCast, smul_eq_mul, mul_one]
      have hc : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- The left Gram defect of the Reynolds average is quadratic in the original
multiplication defect. -/
theorem norm_reynoldsCorrection_star_mul_self_sub_one_le [Nontrivial A]
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    ‖star (reynoldsCorrection φ g) * reynoldsCorrection φ g - 1‖ ≤
      4 * δ ^ 2 := by
  classical
  have hsign : ‖star (reynoldsCorrection φ g) * reynoldsCorrection φ g - 1‖ =
      ‖1 - star (reynoldsCorrection φ g) * reynoldsCorrection φ g‖ := by
    rw [← norm_neg]
    congr 1
    abel
  rw [hsign, ← reynoldsVariance_left φ g, norm_smul]
  calc
    ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ‖∑ x : F,
            star (reynoldsSummand φ g x - reynoldsCorrection φ g) *
              (reynoldsSummand φ g x - reynoldsCorrection φ g)‖ ≤
        ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ∑ x : F,
            ‖star (reynoldsSummand φ g x - reynoldsCorrection φ g) *
              (reynoldsSummand φ g x - reynoldsCorrection φ g)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖((Fintype.card F : ℂ)⁻¹)‖ * ∑ _x : F, (4 * δ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro x _
      rw [CStarRing.norm_star_mul_self]
      have hx := norm_reynoldsSummand_sub_correction_le φ hδ0 hφ g x
      nlinarith [norm_nonneg (reynoldsSummand φ g x - reynoldsCorrection φ g)]
    _ = 4 * δ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [norm_inv, Complex.norm_natCast, smul_eq_mul]
      have hc : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- Polar unitarization changes the Reynolds average only quadratically. -/
theorem norm_polarUnitary_reynoldsCorrection_sub_le [Nontrivial A]
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F)
    (hgram : 4 * δ ^ 2 ≤ 1 / 2) :
    ‖polarUnitary (reynoldsCorrection φ g) - reynoldsCorrection φ g‖ ≤
      8 * δ ^ 2 := by
  have hleft : ‖star (reynoldsCorrection φ g) * reynoldsCorrection φ g - 1‖ ≤
      1 / 2 :=
    (norm_reynoldsCorrection_star_mul_self_sub_one_le φ hδ0 hφ g).trans hgram
  calc
    ‖polarUnitary (reynoldsCorrection φ g) - reynoldsCorrection φ g‖ ≤
        2 * ‖reynoldsCorrection φ g‖ *
          ‖star (reynoldsCorrection φ g) * reynoldsCorrection φ g - 1‖ :=
      norm_polarUnitary_sub_le hleft
    _ ≤ 2 * 1 * (4 * δ ^ 2) := by
      gcongr
      exact norm_reynoldsCorrection_le_one φ g
      exact norm_reynoldsCorrection_star_mul_self_sub_one_le φ hδ0 hφ g
    _ = 8 * δ ^ 2 := by ring

/-- One unitarized Reynolds step. -/
noncomputable def correctedTable [Nontrivial A]
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hφ : MultiplicativeDefectAtMost φ δ) : F → unitary A :=
  fun g ↦
    ⟨polarUnitary (reynoldsCorrection φ g),
      polarUnitary_mem_unitary_of_norm_sub_unitary_le (φ g).prop hδ0 hδ
        (norm_reynoldsCorrection_sub_le φ hδ0 hφ g)⟩

/-- One correction step moves every table entry by at most `6δ`. -/
theorem norm_correctedTable_sub_le [Nontrivial A]
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    ‖((correctedTable φ hδ0 hδ hφ g : unitary A) : A) -
      ((φ g : unitary A) : A)‖ ≤ 6 * δ :=
  norm_polarUnitary_sub_unitary_le (φ g).prop hδ0 hδ
    (norm_reynoldsCorrection_sub_le φ hδ0 hφ g)

/-- A Reynolds-polar correction step squares the multiplication defect, with
a dimension-free constant. -/
theorem correctedTable_multiplicativeDefectAtMost [Nontrivial A]
    (φ : F → unitary A) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hφ : MultiplicativeDefectAtMost φ δ)
    (hgram : 4 * δ ^ 2 ≤ 1 / 2) :
    MultiplicativeDefectAtMost (correctedTable φ hδ0 hδ hφ) (26 * δ ^ 2) := by
  intro g h
  let ψ := correctedTable φ hδ0 hδ hφ
  let Tg := reynoldsCorrection φ g
  let Th := reynoldsCorrection φ h
  let Tgh := reynoldsCorrection φ (g * h)
  have hpolar (x : F) :
      ‖((ψ x : unitary A) : A) - reynoldsCorrection φ x‖ ≤ 8 * δ ^ 2 := by
    change ‖polarUnitary (reynoldsCorrection φ x) - reynoldsCorrection φ x‖ ≤
      8 * δ ^ 2
    exact norm_polarUnitary_reynoldsCorrection_sub_le φ hδ0 hφ x hgram
  have hfirst :
      ‖((ψ g : unitary A) : A) * ((ψ h : unitary A) : A) - Tg * Th‖ ≤
        16 * δ ^ 2 := by
    have hid : ((ψ g : unitary A) : A) * ((ψ h : unitary A) : A) - Tg * Th =
        (((ψ g : unitary A) : A) - Tg) * ((ψ h : unitary A) : A) +
          Tg * (((ψ h : unitary A) : A) - Th) := by
      noncomm_ring
    rw [hid]
    calc
      ‖(((ψ g : unitary A) : A) - Tg) * ((ψ h : unitary A) : A) +
          Tg * (((ψ h : unitary A) : A) - Th)‖ ≤
          ‖(((ψ g : unitary A) : A) - Tg) * ((ψ h : unitary A) : A)‖ +
            ‖Tg * (((ψ h : unitary A) : A) - Th)‖ := norm_add_le _ _
      _ ≤ ‖((ψ g : unitary A) : A) - Tg‖ +
            ‖Tg‖ * ‖((ψ h : unitary A) : A) - Th‖ := by
        gcongr
        · rw [CStarRing.norm_mul_mem_unitary _ (ψ h).prop]
        · exact norm_mul_le _ _
      _ ≤ 8 * δ ^ 2 + 1 * (8 * δ ^ 2) := by
        gcongr
        · exact hpolar g
        · exact norm_reynoldsCorrection_le_one φ g
        · exact hpolar h
      _ = 16 * δ ^ 2 := by ring
  have hlast : ‖Tgh - ((ψ (g * h) : unitary A) : A)‖ ≤ 8 * δ ^ 2 := by
    rw [← norm_neg, neg_sub]
    exact hpolar (g * h)
  have hdecomp :
      ((ψ g : unitary A) : A) * ((ψ h : unitary A) : A) -
          ((ψ (g * h) : unitary A) : A) =
        (((ψ g : unitary A) : A) * ((ψ h : unitary A) : A) - Tg * Th) +
          (Tg * Th - Tgh) + (Tgh - ((ψ (g * h) : unitary A) : A)) := by
    noncomm_ring
  change ‖((ψ (g * h) : unitary A) : A) -
      ((ψ g : unitary A) : A) * ((ψ h : unitary A) : A)‖ ≤ 26 * δ ^ 2
  rw [← norm_neg, neg_sub]
  rw [hdecomp]
  calc
    ‖(((ψ g : unitary A) : A) * ((ψ h : unitary A) : A) - Tg * Th) +
        (Tg * Th - Tgh) + (Tgh - ((ψ (g * h) : unitary A) : A))‖ ≤
      ‖((ψ g : unitary A) : A) * ((ψ h : unitary A) : A) - Tg * Th‖ +
        ‖Tg * Th - Tgh‖ + ‖Tgh - ((ψ (g * h) : unitary A) : A)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 16 * δ ^ 2 + 2 * δ ^ 2 + 8 * δ ^ 2 :=
      add_le_add (add_le_add hfirst
        (norm_reynoldsCorrection_mul_sub_le φ hδ0 hφ g h)) hlast
    _ = 26 * δ ^ 2 := by ring

/-- An already exact representation is fixed by the Reynolds-polar step. -/
theorem correctedTable_eq_of_multiplicative [Nontrivial A]
    (φ : F →* unitary A) (g : F) :
    correctedTable (fun x ↦ φ x) (δ := 0) (by norm_num) (by norm_num)
      (fun x y ↦ by simp) g = φ g := by
  apply Subtype.ext
  have hnorm := norm_correctedTable_sub_le (fun x ↦ φ x)
    (δ := 0) (by norm_num) (by norm_num) (fun x y ↦ by simp) g
  have hzero : ((correctedTable (fun x ↦ φ x) (δ := 0)
      (by norm_num) (by norm_num) (fun x y ↦ by simp) g : unitary A) : A) -
        ((φ g : unitary A) : A) = 0 := by
    simpa only [mul_zero, norm_le_zero_iff] using hnorm
  exact sub_eq_zero.mp hzero

end

end FiniteGroupUlamStep
end GroupApproximation
