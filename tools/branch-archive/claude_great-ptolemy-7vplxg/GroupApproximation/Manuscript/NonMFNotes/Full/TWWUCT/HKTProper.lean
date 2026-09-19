import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAction
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTDecayGen

/-!
# Properness of the action on the Higson--Kasparov--Trout algebra

Lane TWWUCT-C (WO-TWWUCT-C).  If the affine isometric action `b` of the discrete group `G` on
`H` is metrically proper, then the induced action `α` on `A(H)` is proper in the `C₀` sense:
for all `F, F' ∈ A(H)` the function `g ↦ ‖α_g(F) F'‖` vanishes at infinity on `G`
(HKT 1998, §4-5; Higson--Kasparov 2001, §3: `A(H)` is a proper `G`-C⋆-algebra).

The proof: `F` and `F'` vanish at infinity on `ℝ × H` (`decaysRadially_of_mem`), and
`α_g(F)(t, y)` is `F(t, g⁻¹ y)` up to an isometric automorphism.  So `α_g(F) F'` is small
unless some point `y` of a fixed ball has `g⁻¹ y` in the same ball, which happens only for
finitely many `g` (`finite_bounded_return`).

* `AffineIsometricAction.finite_ambientMap_mul`: the ambient statement.
* `AffineIsometricAction.hktAlgebra_isProper`: `{g | ε < ‖α_g(F) F'‖}` is finite.
* `AffineIsometricAction.tendsto_hktAction_mul`: `‖α_g(F) F'‖ → 0` along the cofinite filter.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe u v w

open Filter Topology

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (b : AffineIsometricAction G H)
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- Ambient properness: for radially decaying `F, F'`, only finitely many `g` have
`ε < ‖α_g(F) F'‖`. -/
theorem finite_ambientMap_mul (hb : b.IsMetricallyProper) {F F' : ℝ × H →ᵇ C}
    (hF : DecaysRadially F) (hF' : DecaysRadially F') {ε : ℝ} (hε : 0 < ε) :
    {g : G | ε < ‖b.ambientMap g F * F'‖}.Finite := by
  have hpos : 0 < ‖F‖ + ‖F'‖ + 1 := by positivity
  obtain ⟨δ, hδ, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ (‖F‖ + ‖F'‖ + 1) * δ = ε :=
    ⟨ε / (‖F‖ + ‖F'‖ + 1), div_pos hε hpos, mul_div_cancel₀ ε hpos.ne'⟩
  obtain ⟨R, hR⟩ := hF δ hδ
  obtain ⟨R', hR'⟩ := hF' δ hδ
  refine ((b.finite_bounded_return hb (max R R')).preimage inv_injective.injOn).subset ?_
  intro g hg
  have hg' : ε < ‖b.ambientMap g F * F'‖ := hg
  show ∃ ξ : H, ‖ξ‖ ≤ max R R' ∧ ‖b.act g⁻¹ ξ‖ ≤ max R R'
  by_contra hno
  push_neg at hno
  refine absurd hg' (not_lt.2 ?_)
  rw [BoundedContinuousFunction.norm_le hε.le]
  rintro ⟨t, y⟩
  have hmul : ‖(b.ambientMap g F * F') (t, y)‖ ≤ ‖F (t, b.act g⁻¹ y)‖ * ‖F' (t, y)‖ := by
    show ‖b.ambientMap g F (t, y) * F' (t, y)‖ ≤ _
    rw [ambientMap_apply]
    refine (norm_mul_le _ _).trans_eq ?_
    rw [StarAlgEquiv.norm_map]
  refine hmul.trans ?_
  have hFn := F.norm_coe_le_norm (t, b.act g⁻¹ y)
  have hFn' := F'.norm_coe_le_norm (t, y)
  have hF0 := norm_nonneg F
  have hF'0 := norm_nonneg F'
  have ht0 := abs_nonneg t
  by_cases h1 : R' < |t| + ‖y‖
  · calc ‖F (t, b.act g⁻¹ y)‖ * ‖F' (t, y)‖ ≤ ‖F‖ * δ :=
          mul_le_mul hFn (hR' t y h1) (norm_nonneg _) hF0
      _ ≤ (‖F‖ + ‖F'‖ + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε := hδe
  · have hy : ‖y‖ ≤ max R R' := by
      have hmax := le_max_right R R'
      linarith [not_lt.1 h1]
    have h2 := hno y hy
    have h3 : R < |t| + ‖b.act g⁻¹ y‖ := by
      have hmax := le_max_left R R'
      linarith
    calc ‖F (t, b.act g⁻¹ y)‖ * ‖F' (t, y)‖ ≤ δ * ‖F'‖ :=
          mul_le_mul (hR t _ h3) hFn' (norm_nonneg _) hδ.le
      _ ≤ δ * (‖F‖ + ‖F'‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = ε := (mul_comm _ _).trans hδe

/-- **Properness of the Higson--Kasparov--Trout action** (HKT 1998, §4-5; HK 2001, §3).  For a
metrically proper affine isometric action `b` and `F, F' ∈ A(H)`, only finitely many `g ∈ G`
have `ε < ‖α_g(F) F'‖`. -/
theorem hktAlgebra_isProper (hb : b.IsMetricallyProper) (F F' : HKTAlgebraOf H C) {ε : ℝ}
    (hε : 0 < ε) : {g : G | ε < ‖b.hktAction C g F * F'‖}.Finite := by
  refine (b.finite_ambientMap_mul hb (decaysRadially_of_mem F) (decaysRadially_of_mem F')
    hε).subset ?_
  intro g hg
  have hg' : ε < ‖b.hktAction C g F * F'‖ := hg
  rw [norm_hktAlgebra] at hg'
  exact hg'

/-- The `C₀` form of properness: `‖α_g(F) F'‖ → 0` as `g → ∞` in `G`. -/
theorem tendsto_hktAction_mul (hb : b.IsMetricallyProper) (F F' : HKTAlgebraOf H C) :
    Tendsto (fun g : G => ‖b.hktAction C g F * F'‖) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  refine Filter.eventually_cofinite.2 ((b.hktAlgebra_isProper hb F F' (half_pos hε)).subset ?_)
  intro g hg
  have hg' : ¬dist ‖b.hktAction C g F * F'‖ 0 < ε := hg
  rw [dist_zero_right, norm_norm, not_lt] at hg'
  show ε / 2 < ‖b.hktAction C g F * F'‖
  linarith [half_lt_self hε]

end AffineIsometricAction

end

end GroupApproximation.Full.TWWUCT
