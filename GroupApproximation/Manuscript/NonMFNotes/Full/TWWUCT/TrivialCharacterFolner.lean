import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HaagerupCocycle
import GroupApproximation.Analysis.ReducedGroupCStarTrace

/-!
# Almost invariant unit vectors in `ℓ²(G)` for an amenable group

Lane TWWUCT (work order WO-TWWCore-2).  This is the first step of Hulanicki's
theorem.  If `G` is amenable, the trivial representation is weakly contained in
the left regular representation, so `C⋆_r(G)` has a character `χ` with
`χ(λ_g) = 1`.  This file proves the geometric input.

Normalised indicator vectors `ξₙ = |Aₙ|^{-1/2} 1_{Aₙ}` of the Følner sets from
`FolnerData` satisfy `‖ξₙ‖ = 1` and `‖λ_g ξₙ - ξₙ‖ → 0` for every `g`.  The
estimate is `‖λ_g 1_A - 1_A‖² ≤ |∂_g A| + |∂_{g⁻¹} A|`, which is
`sum_jump_sq_le` from `HaagerupCocycle`.

* `indicatorVec`, `indicatorVec_apply`, `card_le_norm_indicatorVec_sq`.
* `norm_leftRegular_indicatorVec_sub_le`.
* `unitVec`, `norm_unitVec`, `norm_leftRegular_unitVec_sub_sq_le`.
* `AlmostInvariantVectors`, `exists_almostInvariantVectors`.
-/

namespace GroupApproximation.Full.TWWUCT

open Filter Topology ReducedGroupCStarTrace
open scoped ENNReal

universe u

variable {G : Type u} [Group G]

open Classical in
/-- The indicator vector `1_A ∈ ℓ²(G)` of a finite set `A`. -/
noncomputable def indicatorVec (A : Finset G) : GroupHilbert G :=
  ⟨fun x ↦ if x ∈ A then (1 : ℂ) else 0, by
    refine (memℓp_zero ?_).of_exponent_ge zero_le
    refine A.finite_toSet.subset fun x hx ↦ Finset.mem_coe.mpr ?_
    by_contra h
    simp [h] at hx⟩

open Classical in
theorem indicatorVec_apply (A : Finset G) (x : G) :
    indicatorVec A x = if x ∈ A then (1 : ℂ) else 0 :=
  rfl

/-- `|A| ≤ ‖1_A‖²`. -/
theorem card_le_norm_indicatorVec_sq (A : Finset G) :
    (A.card : ℝ) ≤ ‖indicatorVec A‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hone : ∀ x ∈ A, ‖indicatorVec A x‖ ^ (2 : ℝ≥0∞).toReal = 1 := fun x hx ↦ by
    rw [indicatorVec_apply, if_pos hx, norm_one, Real.one_rpow]
  calc (A.card : ℝ) = ∑ x ∈ A, ‖indicatorVec A x‖ ^ (2 : ℝ≥0∞).toReal := by
        rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ‖indicatorVec A‖ ^ (2 : ℝ≥0∞).toReal := lp.sum_rpow_le_norm_rpow hp _ _
    _ = ‖indicatorVec A‖ ^ 2 := rpow_two_toReal _

/-- `(λ_g 1_A - 1_A)(x)` is the jump `1_A(g⁻¹x) - 1_A(x)`. -/
theorem leftRegular_indicatorVec_sub_apply (A : Finset G) (g x : G) :
    (leftRegular G g (indicatorVec A) - indicatorVec A) x = (jump A g x : ℂ) := by
  simp only [lp.coeFn_sub, Pi.sub_apply, leftRegular_apply, indicatorVec_apply, jump]
  split_ifs <;> simp

/-- `‖λ_g 1_A - 1_A‖ ≤ (|∂_g A| + |∂_{g⁻¹} A|)^{1/2}`. -/
theorem norm_leftRegular_indicatorVec_sub_le (A : Finset G) (g : G) :
    ‖leftRegular G g (indicatorVec A) - indicatorVec A‖ ≤
      Real.sqrt (((AmenableActionSofic.boundary A g).card : ℝ) +
        (AmenableActionSofic.boundary A g⁻¹).card) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hb : (0 : ℝ) ≤ ((AmenableActionSofic.boundary A g).card : ℝ) +
      (AmenableActionSofic.boundary A g⁻¹).card := by positivity
  refine lp.norm_le_of_forall_sum_le hp (Real.sqrt_nonneg _) fun s ↦ ?_
  simp only [leftRegular_indicatorVec_sub_apply, Complex.norm_real, norm_rpow_two_toReal,
    rpow_two_toReal, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt hb]
  exact sum_jump_sq_le A g s

/-- The normalised indicator vector `‖1_A‖⁻¹ 1_A`. -/
noncomputable def unitVec (A : Finset G) : GroupHilbert G :=
  ((‖indicatorVec A‖⁻¹ : ℝ) : ℂ) • indicatorVec A

theorem norm_indicatorVec_sq_pos {A : Finset G} (hA : A.Nonempty) :
    0 < ‖indicatorVec A‖ ^ 2 := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  exact hcard.trans_le (card_le_norm_indicatorVec_sq A)

theorem norm_unitVec {A : Finset G} (hA : A.Nonempty) : ‖unitVec A‖ = 1 := by
  have hne : ‖indicatorVec A‖ ≠ 0 := by
    intro h
    have := norm_indicatorVec_sq_pos hA
    rw [h] at this
    norm_num at this
  rw [unitVec, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hne]

/-- `‖λ_g ξ_A - ξ_A‖² ≤ (|∂_g A| + |∂_{g⁻¹} A|) / |A|`. -/
theorem norm_leftRegular_unitVec_sub_sq_le {A : Finset G} (hA : A.Nonempty) (g : G) :
    ‖leftRegular G g (unitVec A) - unitVec A‖ ^ 2 ≤
      (((AmenableActionSofic.boundary A g).card : ℝ) +
        (AmenableActionSofic.boundary A g⁻¹).card) / A.card := by
  set b : ℝ := ((AmenableActionSofic.boundary A g).card : ℝ) +
    (AmenableActionSofic.boundary A g⁻¹).card with hbdef
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb : 0 ≤ b := by rw [hbdef]; positivity
  have hv := card_le_norm_indicatorVec_sq A
  have hv0 := norm_indicatorVec_sq_pos hA
  have hw2 : ‖leftRegular G g (indicatorVec A) - indicatorVec A‖ ^ 2 ≤ b := by
    calc ‖leftRegular G g (indicatorVec A) - indicatorVec A‖ ^ 2
        ≤ (Real.sqrt b) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_leftRegular_indicatorVec_sub_le A g) 2
      _ = b := Real.sq_sqrt hb
  have heq : leftRegular G g (unitVec A) - unitVec A =
      ((‖indicatorVec A‖⁻¹ : ℝ) : ℂ) •
        (leftRegular G g (indicatorVec A) - indicatorVec A) := by
    rw [unitVec, map_smul, smul_sub]
  rw [heq, norm_smul, mul_pow, Complex.norm_real, norm_inv, norm_norm, inv_pow,
    inv_mul_le_iff₀ hv0]
  calc ‖leftRegular G g (indicatorVec A) - indicatorVec A‖ ^ 2 ≤ b := hw2
    _ = A.card * (b / A.card) := (mul_div_cancel₀ b hcard.ne').symm
    _ ≤ ‖indicatorVec A‖ ^ 2 * (b / A.card) :=
      mul_le_mul_of_nonneg_right hv (div_nonneg hb hcard.le)

/-- A sequence of unit vectors in `ℓ²(G)` that is asymptotically invariant under
every left translation. -/
structure AlmostInvariantVectors (G : Type u) [Group G] where
  vec : ℕ → GroupHilbert G
  norm_vec : ∀ n, ‖vec n‖ = 1
  tendsto : ∀ g : G, Tendsto (fun n ↦ ‖leftRegular G g (vec n) - vec n‖) atTop (𝓝 0)

/-- A countable amenable group has almost invariant unit vectors in `ℓ²(G)`. -/
theorem exists_almostInvariantVectors [Countable G] (hG : Amenability.IsAmenable G) :
    Nonempty (AlmostInvariantVectors G) := by
  obtain ⟨D⟩ := exists_folnerData hG
  refine ⟨⟨fun n ↦ unitVec (D.sets n), fun n ↦ norm_unitVec (D.nonempty n), fun g ↦ ?_⟩⟩
  obtain ⟨k, rfl⟩ := D.seq_surj g
  have h4 : Tendsto (fun n : ℕ ↦ 2 * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul 2
    rwa [mul_zero] at this
  have hsq : Tendsto (fun n ↦ ‖leftRegular G (D.seq k) (unitVec (D.sets n)) -
      unitVec (D.sets n)‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity)
      ((eventually_gt_atTop k).mono fun n hn ↦ ?_) h4
    have hcard : (0 : ℝ) < (D.sets n).card := by exact_mod_cast (D.nonempty n).card_pos
    obtain ⟨h1, h2⟩ := D.small n k hn
    refine (norm_leftRegular_unitVec_sub_sq_le (D.nonempty n) (D.seq k)).trans ?_
    rw [div_le_iff₀ hcard]
    linarith
  have hsqrt := hsq.sqrt
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun n ↦ Real.sqrt_sq (norm_nonneg _)

end GroupApproximation.Full.TWWUCT
