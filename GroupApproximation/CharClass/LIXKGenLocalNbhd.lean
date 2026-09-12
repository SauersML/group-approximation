import GroupApproximation.CharClass.LIXKGenLocalPair
import GroupApproximation.CharClass.LIXHsqNeighbourhood
import GroupApproximation.Meta.AxiomGuard

/-!
# The neighbourhood of the `i`-th zero the compatibility square is compared on, at rank `n`

Lane `lix-oddside-n` (chart side of `KGenLocalNonzero`).

This is the rank-`n`, `k`-zero counterpart of `CharClass/LIXHsqNeighbourhood.lean`, over
`CharClass/LIXKGenLocalPair.lean`'s `lixKTrivBall n k dd i` and
`CharClass/LIXKGenBaseChart.lean`'s `lixKBC`/`lixKFC n k dd i`.  The generic restriction lemma
`RelativeSupport.injective_relPullback_subInclusion` is reused.

## The cap, and the one change from rank two

The ball the square is compared on is the ball `lixKTrivBall` was cut at, capped so that the
chart clamps are inactive.  At rank two the cap is `1/2`: a point of norm `< 1/2` in the sup norm
has three coordinates of absolute value `< 1/2`, so `sphereQ < 3/4 ≤ 1`.  At rank `n` the sphere
chart's radial quantity `chartQ n w = w₁² + ∑ⱼ ‖vⱼ‖²` has `n + 1` terms, and `1/2` is too large
as soon as `n ≥ 3`.  The cap here is `1/(n+2)`, giving `chartQ n < (n+1)/(n+2)² < 1`, and the
circle coordinate is still `< 1/2`.

## Main declarations

* `KGen.lixKHsqRad`, `KGen.lixKHsqBall` — the capped ball in chart coordinates, with
  `lixKBC_image_lixKHsqBall_subset`, `lixKHsqBall_subset_bc_source`,
  `lixKHsqBall_subset_fc_source`, `zero_mem_lixKHsqBall`.
* `KGen.norm_lt_half_of_mem_lixKHsqBall`, `chartQ_lt_one_of_mem_lixKHsqBall`,
  `chartQ_le_one_of_mem_lixKHsqBall`, `circCoord_mem_Ioo_of_mem_lixKHsqBall` — the clamps are
  inactive on the ball.
* `KGen.smul_mem_lixKHsqBall` — the ball is star-shaped about the origin.
* `KGen.lixKU` — its image in the local model, with `isOpen_lixKU`, `zero_mem_lixKU`,
  `lixKU_subset_target`, `symm_mem_lixKHsqBall`.
* `KGen.lixKULine` — the relative group of `(lixKU, lixKU ∖ 0)` in the top degree is a line.
* `KGen.lixKShrinkMap`, `KGen.injective_lixKShrink` — restricting from the chart's target to
  `lixKU` is injective.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open Set CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The capped ball in chart coordinates -/

/-- The radius `lixKTrivBall` was cut at. -/
def lixKHsqEps (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) : ℝ :=
  lixKBaseEps n k dd i (lixKTrivSet n k dd i hGc hGu) (isOpen_lixKTrivSet n k dd i hGc hGu)
    (lixKZero_mem_lixKTrivSet n k dd i hGc hGu)

/-- The radius the square is compared at: `lixKHsqEps`, capped at `1/(n+2)`. -/
def lixKHsqRad (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) : ℝ :=
  min (lixKHsqEps n k dd i hGc hGu) (1 / ((n : ℝ) + 2))

/-- **The ball in chart coordinates**, whose base chart image lies inside `lixKTrivBall`. -/
def lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Set (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :=
  Metric.ball 0 (lixKHsqRad n k dd i hGc hGu)

theorem lixKHsqBall_subset_pre (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKHsqBall n k dd i hGc hGu ⊆ Metric.ball 0 (lixKHsqEps n k dd i hGc hGu) :=
  Metric.ball_subset_ball (min_le_left _ _)

theorem lixKBC_image_lixKHsqBall_subset (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (lixKBC n k dd i) '' lixKHsqBall n k dd i hGc hGu ⊆ lixKTrivBall n k dd i hGc hGu :=
  Set.image_mono (lixKHsqBall_subset_pre n k dd i hGc hGu)

theorem lixKHsqBall_subset_bc_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKHsqBall n k dd i hGc hGu ⊆ (lixKBC n k dd i).source :=
  fun _ hw => (lixKBaseBallPre_subset n k dd i (lixKTrivSet n k dd i hGc hGu)
    (isOpen_lixKTrivSet n k dd i hGc hGu) (lixKZero_mem_lixKTrivSet n k dd i hGc hGu)
    (lixKHsqBall_subset_pre n k dd i hGc hGu hw)).1

theorem lixKHsqBall_subset_fc_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKHsqBall n k dd i hGc hGu ⊆ (lixKFC n k dd i).source := by
  rw [← lixKBC_source_eq_lixKFC_source n k dd i]
  exact lixKHsqBall_subset_bc_source n k dd i hGc hGu

theorem lixKHsqRad_pos (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    0 < lixKHsqRad n k dd i hGc hGu :=
  lt_min (lixKBaseEps_pos n k dd i _ _ _) (by positivity)

theorem zero_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (0 : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ lixKHsqBall n k dd i hGc hGu :=
  Metric.mem_ball_self (lixKHsqRad_pos n k dd i hGc hGu)

/-! ## 2. The clamps are inactive on the ball -/

theorem norm_mul_lt_one_of_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)} (hq : q ∈ lixKHsqBall n k dd i hGc hGu) :
    ‖q‖ * ((n : ℝ) + 2) < 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h : ‖q‖ < 1 / ((n : ℝ) + 2) :=
    lt_of_lt_of_le (mem_ball_zero_iff.mp hq) (min_le_right _ _)
  exact (lt_div_iff₀ hpos).mp h

/-- Every point of the ball has norm `< 1/2`, the cap `1/(n+2)` being at most `1/2`. -/
theorem norm_lt_half_of_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)} (hq : q ∈ lixKHsqBall n k dd i hGc hGu) :
    ‖q‖ < 1 / 2 := by
  have hn := norm_mul_lt_one_of_mem_lixKHsqBall n k dd i hGc hGu hq
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  nlinarith [mul_nonneg hq0 hn0]

/-- **The sphere chart's clamp is inactive on the ball**: `chartQ n < 1`. -/
theorem chartQ_lt_one_of_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)} (hq : q ∈ lixKHsqBall n k dd i hGc hGu) :
    chartQ n q.1.1 < 1 := by
  have hn := norm_mul_lt_one_of_mem_lixKHsqBall n k dd i hGc hGu hq
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have h1 : ‖q.1.1‖ ≤ ‖q‖ := le_trans (norm_fst_le q.1) (norm_fst_le q)
  have hc : |q.1.1.1| ≤ ‖q‖ := by
    have := le_trans (norm_fst_le q.1.1) h1
    rwa [Real.norm_eq_abs] at this
  have hv : ∀ j, ‖q.1.1.2 j‖ ≤ ‖q‖ := fun j =>
    le_trans (norm_le_pi_norm q.1.1.2 j) (le_trans (norm_snd_le q.1.1) h1)
  have hc2 : q.1.1.1 ^ 2 ≤ ‖q‖ ^ 2 := by
    nlinarith [abs_nonneg q.1.1.1, sq_abs q.1.1.1]
  have hv2 : ∑ j, ‖q.1.1.2 j‖ ^ 2 ≤ (n : ℝ) * ‖q‖ ^ 2 := by
    have hs : ∑ j : Fin n, ‖q.1.1.2 j‖ ^ 2 ≤ ∑ _j : Fin n, ‖q‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hv j) 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    exact hs
  have hx : ‖q‖ * ‖q‖ * (((n : ℝ) + 2) * ((n : ℝ) + 2)) < 1 := by
    have hm : 0 ≤ ‖q‖ * ((n : ℝ) + 2) := mul_nonneg hq0 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hn.le hm]
  show q.1.1.1 ^ 2 + ∑ j : Fin n, ‖q.1.1.2 j‖ ^ 2 < 1
  nlinarith [mul_nonneg hq0 hq0, mul_nonneg (mul_nonneg hq0 hq0) hn0,
    mul_nonneg (mul_nonneg hq0 hq0) (sq_nonneg (n : ℝ))]

/-- The sphere chart's clamp is inactive on the ball, in the non-strict form. -/
theorem chartQ_le_one_of_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)} (hq : q ∈ lixKHsqBall n k dd i hGc hGu) :
    chartQ n q.1.1 ≤ 1 :=
  (chartQ_lt_one_of_mem_lixKHsqBall n k dd i hGc hGu hq).le

/-- **The circle chart's clamp is inactive on the ball.** -/
theorem circCoord_mem_Ioo_of_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)} (hq : q ∈ lixKHsqBall n k dd i hGc hGu) :
    q.1.2 ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hn := norm_mul_lt_one_of_mem_lixKHsqBall n k dd i hGc hGu hq
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hlt : ‖q‖ < 1 := by nlinarith [mul_nonneg hq0 hn0]
  have hc : |q.1.2| ≤ ‖q‖ := by
    have := le_trans (norm_snd_le q.1) (norm_fst_le q)
    rwa [Real.norm_eq_abs] at this
  have := abs_lt.mp (lt_of_le_of_lt hc hlt)
  exact ⟨this.1, this.2⟩

/-- **The ball is star-shaped about the origin.** -/
theorem smul_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)} (hq : q ∈ lixKHsqBall n k dd i hGc hGu)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s • q ∈ lixKHsqBall n k dd i hGc hGu :=
  (convex_ball (0 : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) _).smul_mem_of_zero_mem
    (zero_mem_lixKHsqBall n k dd i hGc hGu) hq hs

/-! ## 3. Its image in the local model -/

/-- **The neighbourhood of the origin of the local model** the square is compared on. -/
def lixKU (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Set (Fin (lixRank n dd) → ℂ) :=
  (lixKFC n k dd i) '' lixKHsqBall n k dd i hGc hGu

theorem isOpen_lixKU (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    IsOpen (lixKU n k dd i hGc hGu) :=
  ((lixKFC n k dd i).isOpen_image_iff_of_subset_source
    (lixKHsqBall_subset_fc_source n k dd i hGc hGu)).mpr Metric.isOpen_ball

theorem zero_mem_lixKU (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (0 : Fin (lixRank n dd) → ℂ) ∈ lixKU n k dd i hGc hGu :=
  ⟨(0, 0), zero_mem_lixKHsqBall n k dd i hGc hGu, lixKFullChart_zero n dd⟩

theorem lixKU_subset_target (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKU n k dd i hGc hGu ⊆ (lixKFC n k dd i).target := by
  rw [lixKU, ← (lixKFC n k dd i).image_source_eq_target]
  exact Set.image_mono (lixKHsqBall_subset_fc_source n k dd i hGc hGu)

theorem symm_mem_lixKHsqBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {v : Fin (lixRank n dd) → ℂ} (hv : v ∈ lixKU n k dd i hGc hGu) :
    (lixKFC n k dd i).symm v ∈ lixKHsqBall n k dd i hGc hGu := by
  obtain ⟨q, hq, rfl⟩ := hv
  rwa [(lixKFC n k dd i).left_inv (lixKHsqBall_subset_fc_source n k dd i hGc hGu hq)]

/-! ## 4. The pair over it is a line -/

/-- **The relative group of `(lixKU, lixKU ∖ 0)` in the top degree is a line.** -/
def lixKULine (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ↥(relCohomology (ZMod 2) (TopCat.of ↥(lixKU n k dd i hGc hGu))
        ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ))) (2 * lixRank n dd)) ≃ₗ[ZMod 2] ZMod 2 :=
  ((excisionIsoPoint (TopCat.of (Fin (lixRank n dd) → ℂ)) 0 (lixKU n k dd i hGc hGu)
      (isOpen_lixKU n k dd i hGc hGu) (zero_mem_lixKU n k dd i hGc hGu)
      (2 * lixRank n dd)).symm).toLinearEquiv.trans (localEquiv (lixRank n dd))

/-! ## 5. Restricting from the chart's target to it -/

/-- The inclusion of `lixKU` into the chart's target. -/
def lixKShrinkMap (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of ↥(lixKU n k dd i hGc hGu) ⟶ TopCat.of ↥(lixKFC n k dd i).target :=
  subInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ)) (lixKU_subset_target n k dd i hGc hGu)

theorem lixKShrink_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ))),
      (ConcreteCategory.hom (lixKShrinkMap n k dd i hGc hGu)) x ∈
        ((Subtype.val : ↥(lixKFC n k dd i).target → (Fin (lixRank n dd) → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ))) :=
  fun _ hx => hx

/-- **Restricting from the chart's target to `lixKU` is injective.** -/
theorem injective_lixKShrink (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Function.Injective (relPullback (ZMod 2) (lixKShrinkMap n k dd i hGc hGu)
      (lixKShrink_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)).hom :=
  RelativeSupport.injective_relPullback_subInclusion
    (X := TopCat.of (Fin (lixRank n dd) → ℂ)) (0 : Fin (lixRank n dd) → ℂ)
    (isOpen_lixKU n k dd i hGc hGu) (lixKFC n k dd i).open_target
    (zero_mem_lixKU n k dd i hGc hGu) (zero_mem_lixKFC_target n k dd i)
    (lixKU_subset_target n k dd i hGc hGu) (lixKShrink_mapsTo n k dd i hGc hGu)
    (2 * lixRank n dd)

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.chartQ_lt_one_of_mem_lixKHsqBall
#audit_axioms KGen.circCoord_mem_Ioo_of_mem_lixKHsqBall
#audit_axioms KGen.injective_lixKShrink

end GroupApproximation.CharClass
