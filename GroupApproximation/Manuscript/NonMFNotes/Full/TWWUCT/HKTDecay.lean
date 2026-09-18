import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAlgebraDef

/-!
# Radial decay of functions on `ℝ × H`

Lane TWWUCT-C (WO-TWWUCT-C).  Every element of the Higson--Kasparov--Trout algebra `A(H)`
vanishes at infinity in the norm of `ℝ × H` (HKT 1998, §4: the generators are Schwartz in the
radial variable and `C₀` along the stage).  This is the analytic input for the properness of the
induced action.  This file sets up the predicate and its closure properties.

* `DecaysRadially F`: `‖F (t, y)‖ ≤ ε` once `|t| + ‖y‖` is large.
* `decaySubalgebra C`: such functions form a closed non-unital ⋆-subalgebra of `ℝ × H →ᵇ C`.
* `exists_two_add_mul_exp_neg_le`: `(2 + s) e^{-s} → 0`.
* `FinDimAffine.IsStageCoeff.exists_norm_le`: stage coefficients are small far out in `V`.
* `FinDimAffine.norm_le_base_add_foot_add_perp`: `‖y‖ ≤ ‖a‖ + ‖foot y‖ + ‖perp y‖`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe v w

open Filter Topology

section Decay

variable {H : Type v} [NormedAddCommGroup H]
variable {C : Type w} [CStarAlgebra C]

/-- `F` vanishes at infinity in the norm of `ℝ × H`. -/
def DecaysRadially (F : ℝ × H →ᵇ C) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ (t : ℝ) (y : H), R < |t| + ‖y‖ → ‖F (t, y)‖ ≤ ε

theorem decaysRadially_zero : DecaysRadially (0 : ℝ × H →ᵇ C) := by
  intro ε hε
  refine ⟨0, fun t y _ => ?_⟩
  show ‖(0 : C)‖ ≤ ε
  rw [norm_zero]
  exact hε.le

theorem DecaysRadially.add {F G : ℝ × H →ᵇ C} (hF : DecaysRadially F) (hG : DecaysRadially G) :
    DecaysRadially (F + G) := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := hF (ε / 2) (half_pos hε)
  obtain ⟨R₂, hR₂⟩ := hG (ε / 2) (half_pos hε)
  refine ⟨max R₁ R₂, fun t y hty => ?_⟩
  show ‖F (t, y) + G (t, y)‖ ≤ ε
  calc ‖F (t, y) + G (t, y)‖ ≤ ‖F (t, y)‖ + ‖G (t, y)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add (hR₁ t y (lt_of_le_of_lt (le_max_left _ _) hty))
          (hR₂ t y (lt_of_le_of_lt (le_max_right _ _) hty))
    _ = ε := add_halves ε

theorem DecaysRadially.mul_left (F : ℝ × H →ᵇ C) {G : ℝ × H →ᵇ C} (hG : DecaysRadially G) :
    DecaysRadially (F * G) := by
  intro ε hε
  have hF1 : 0 < ‖F‖ + 1 := by positivity
  obtain ⟨R, hR⟩ := hG (ε / (‖F‖ + 1)) (div_pos hε hF1)
  refine ⟨R, fun t y hty => ?_⟩
  show ‖F (t, y) * G (t, y)‖ ≤ ε
  calc ‖F (t, y) * G (t, y)‖ ≤ ‖F (t, y)‖ * ‖G (t, y)‖ := norm_mul_le _ _
    _ ≤ (‖F‖ + 1) * (ε / (‖F‖ + 1)) :=
        mul_le_mul ((F.norm_coe_le_norm _).trans (le_add_of_nonneg_right zero_le_one))
          (hR t y hty) (norm_nonneg _) hF1.le
    _ = ε := mul_div_cancel₀ ε hF1.ne'

theorem DecaysRadially.star {F : ℝ × H →ᵇ C} (hF : DecaysRadially F) :
    DecaysRadially (star F) := by
  intro ε hε
  obtain ⟨R, hR⟩ := hF ε hε
  refine ⟨R, fun t y hty => ?_⟩
  show ‖star (F (t, y))‖ ≤ ε
  rw [norm_star]
  exact hR t y hty

theorem DecaysRadially.smul {F : ℝ × H →ᵇ C} (hF : DecaysRadially F) (c : ℂ) :
    DecaysRadially (c • F) := by
  intro ε hε
  have hc1 : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨R, hR⟩ := hF (ε / (‖c‖ + 1)) (div_pos hε hc1)
  refine ⟨R, fun t y hty => ?_⟩
  show ‖c • F (t, y)‖ ≤ ε
  rw [norm_smul]
  calc ‖c‖ * ‖F (t, y)‖ ≤ (‖c‖ + 1) * (ε / (‖c‖ + 1)) :=
        mul_le_mul (le_add_of_nonneg_right zero_le_one) (hR t y hty) (norm_nonneg _) hc1.le
    _ = ε := mul_div_cancel₀ ε hc1.ne'

theorem isClosed_setOf_decaysRadially :
    IsClosed {F : ℝ × H →ᵇ C | DecaysRadially F} := by
  refine isClosed_of_closure_subset fun F hF => ?_
  show DecaysRadially F
  intro ε hε
  obtain ⟨G, hG, hFG⟩ := Metric.mem_closure_iff.1 hF (ε / 2) (half_pos hε)
  have hG' : DecaysRadially G := hG
  obtain ⟨R, hR⟩ := hG' (ε / 2) (half_pos hε)
  refine ⟨R, fun t y hty => ?_⟩
  have h1 : ‖F (t, y) - G (t, y)‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    exact (BoundedContinuousFunction.dist_coe_le_dist (f := F) (g := G) (t, y)).trans hFG.le
  calc ‖F (t, y)‖ = ‖(F (t, y) - G (t, y)) + G (t, y)‖ := by rw [sub_add_cancel]
    _ ≤ ‖F (t, y) - G (t, y)‖ + ‖G (t, y)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 (hR t y hty)
    _ = ε := add_halves ε

variable (H C) in
/-- The functions vanishing at infinity in the norm of `ℝ × H`, as a non-unital
⋆-subalgebra. -/
def decaySubalgebra : NonUnitalStarSubalgebra ℂ (ℝ × H →ᵇ C) where
  carrier := {F | DecaysRadially F}
  add_mem' {F G} hF hG := DecaysRadially.add (F := F) (G := G) hF hG
  zero_mem' := decaysRadially_zero
  mul_mem' {F _} _ hG := DecaysRadially.mul_left F hG
  smul_mem' c F hF := DecaysRadially.smul (F := F) hF c
  star_mem' {F} hF := DecaysRadially.star (F := F) hF

theorem mem_decaySubalgebra {F : ℝ × H →ᵇ C} : F ∈ decaySubalgebra H C ↔ DecaysRadially F :=
  Iff.rfl

theorem isClosed_decaySubalgebra : IsClosed (decaySubalgebra H C : Set (ℝ × H →ᵇ C)) :=
  isClosed_setOf_decaysRadially

end Decay

/-- `(2 + s) e^{-s} ≤ ε` for all large `s`. -/
theorem exists_two_add_mul_exp_neg_le {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s : ℝ, S ≤ s → (2 + s) * Real.exp (-s) ≤ ε := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h : Tendsto (fun s : ℝ => (2 + s) * Real.exp (-s)) atTop (𝓝 0) := by
    have h3 := (h2.const_mul 2).add h1
    rw [mul_zero, zero_add] at h3
    refine h3.congr fun s => ?_
    show 2 * Real.exp (-s) + s ^ 1 * Real.exp (-s) = (2 + s) * Real.exp (-s)
    ring
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.1 (h.eventually (ge_mem_nhds hε))
  exact ⟨S, hS⟩

namespace FinDimAffine

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- A stage coefficient `k ∈ C₀(V, Cliff(V))` is small far out in `V`. -/
theorem IsStageCoeff.exists_norm_le {E : FinDimAffine H} {k : E.dir →ᵇ C}
    (hk : E.IsStageCoeff k) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ v : E.dir, M < ‖v‖ → ‖k v‖ ≤ ε := by
  obtain ⟨t, ht, hts⟩ :=
    Filter.mem_cocompact.1 (Filter.mem_map.1 (hk.1 (Metric.closedBall_mem_nhds (0 : C) hε)))
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E.dir)).1 ht.isBounded
  refine ⟨M, fun v hv => ?_⟩
  have hvt : v ∉ t := fun hvt => by
    have hvM := hM hvt
    rw [Metric.mem_closedBall, dist_zero_right] at hvM
    exact absurd hvM (not_le.2 hv)
  have hkv := hts (Set.mem_compl hvt)
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hkv
  exact hkv

variable (E : FinDimAffine H)

theorem eq_base_add_foot_add_perp (y : H) : y = E.base + (E.foot y : H) + E.perp y := by
  show y = E.base + E.dir.starProjection (y - E.base) +
    ((y - E.base) - E.dir.starProjection (y - E.base))
  abel

theorem norm_le_base_add_foot_add_perp (y : H) :
    ‖y‖ ≤ ‖E.base‖ + ‖E.foot y‖ + ‖E.perp y‖ := by
  have h := norm_add₃_le (a := E.base) (b := (E.foot y : H)) (c := E.perp y)
  rw [← E.eq_base_add_foot_add_perp y] at h
  exact h

/-- `|t| + ‖perp y‖ ≤ 2 + (t² + ‖perp y‖²)`. -/
theorem abs_add_norm_perp_le (t : ℝ) (y : H) :
    |t| + ‖E.perp y‖ ≤ 2 + E.radiusSq (t, y) := by
  show |t| + ‖E.perp y‖ ≤ 2 + (t ^ 2 + ‖E.perp y‖ ^ 2)
  nlinarith [sq_nonneg (|t| - 1), sq_nonneg (‖E.perp y‖ - 1), sq_abs t, abs_nonneg t,
    norm_nonneg (E.perp y), sq_nonneg t, sq_nonneg ‖E.perp y‖]

end FinDimAffine

end

end GroupApproximation.Full.TWWUCT
