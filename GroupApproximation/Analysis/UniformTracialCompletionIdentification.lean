import GroupApproximation.Analysis.UniformTracialTwoNullIdeal

/-!
# `M = ℂ1 + J`: both inclusions of the audit's (A8)

Let `A = unitization(⊕_s D_s)` be realized inside the bounded product
`∏_s D_s` as `unitizedC0Sum D`, and let `J` be the uniform two-null ideal of
`Analysis/UniformTracialTwoNullIdeal`.  Write `M` for the set of bounded
sequences which are limits, uniformly over all coordinates and along one
operator-norm bounded sequence, of elements of `A`.  That is the predicate
`IsBoundedUniformTwoApproximable` of
`Analysis/UniformTracialSequenceCompletion`; it is stated for bounded
sequences only, so no completion object is postulated anywhere.

This file proves

* `scalarPlusJ_eq_boundedUniformTwoClosure`: `M = ℂ1 + J`, an equality of sets.

  The forward inclusion is the audit's (A9), the tail truncation, supplied by
  the landed `scalarTruncations_bounded_uniformly_approximate`.  The converse
  is `mem_scalarPlusJ_of_uniformTwoLimit`: a uniform two-limit of elements of
  `ℂ1 + J` again lies in `ℂ1 + J`.  The scalar coefficients of the
  approximants are forced to converge because the gauge is normalized at the
  unit — this is exactly `TracialTwoGauge.q_algebraMap`.

* `exists_boundedCStarSequence_uniformTwoLimit`: under the audit's
  coordinatewise finite-rank comparison `‖a‖ ≤ sqrt(s+1) ‖a‖_{2,s}` (here an
  arbitrary coordinate constant), a uniformly bounded, uniformly two-Cauchy
  sequence converges *coordinatewise in operator norm*, and the coordinate
  limits assemble into a bounded sequence which is its uniform two-limit.
  This is the step showing the completion is realized inside the bounded
  product and produces no exotic elements.

* `exists_mem_scalarPlusJ_of_uniformTwoCauchy`: the two combined, which is the
  converse half of (A8) exactly as the audit states it.

`exists_uniformTwoCauchy_scalarTruncations` records that these hypotheses are
inhabited: every element of `ℂ1 + J` supplies such a sequence, namely its own
scalar truncations.
-/

namespace GroupApproximation
namespace UniformTracialCompletionIdentification

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## `ℂ1 + J` is closed under uniform two-limits -/

/-- A uniformly two-convergent sequence is uniformly two-Cauchy. -/
theorem uniformTwoCauchy_of_uniformTwoConvergent (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D} {a : ℕ → BoundedCStarSequence D}
    (hconv : ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (x n - a k n) < ε) :
    ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
      G.q n (a k n - a l n) < ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := hconv (ε / 2) (by linarith)
  refine ⟨K, fun k hk l hl n ↦ ?_⟩
  have t1 : G.q n (a k n - a l n)
      ≤ G.q n (a k n - x n) + G.q n (x n - a l n) :=
    G.sub_le_sub_add_sub n _ (x n) _
  have e1 : G.q n (a k n - x n) = G.q n (x n - a k n) := G.sub_comm_eq n _ _
  have h1 : G.q n (x n - a k n) < ε / 2 := hK k hk n
  have h2 : G.q n (x n - a l n) < ε / 2 := hK l hl n
  linarith

/-- **The converse inclusion of (A8).**  A bounded sequence which is the
uniform two-limit of a sequence of elements of `ℂ1 + J` again lies in
`ℂ1 + J`.

The scalar coefficients of the approximants form a Cauchy sequence: since
`q n 1 = 1`, the modulus of the difference of two coefficients equals a
coordinate gauge, and that is controlled at every coordinate by the two
uniform two-distances plus a coordinate error which tends to zero. -/
theorem mem_scalarPlusJ_of_uniformTwoLimit (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D} {a : ℕ → BoundedCStarSequence D}
    (ha : ∀ k, a k ∈ scalarPlusJ G)
    (hconv : ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (x n - a k n) < ε) :
    x ∈ scalarPlusJ G := by
  have ha' : ∀ k, ∃ c : ℂ,
      Tendsto (fun n ↦ G.q n (a k n - algebraMap ℂ (D n) c)) atTop (nhds 0) := by
    intro k
    have hk := ha k
    rw [scalarPlusJ_eq_scalarPlusTwoNull] at hk
    exact hk
  choose c hc using ha'
  -- the coefficients are Cauchy
  have hcauchy : CauchySeq c := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := hconv (ε / 4) (by linarith)
    refine ⟨K, fun k hk l hl ↦ ?_⟩
    have hbound : ∀ n : ℕ, ‖c k - c l‖
        ≤ (G.q n (a k n - algebraMap ℂ (D n) (c k))
            + G.q n (a l n - algebraMap ℂ (D n) (c l))) + ε / 2 := by
      intro n
      have t1 : G.q n (algebraMap ℂ (D n) (c k) - algebraMap ℂ (D n) (c l))
          ≤ G.q n (algebraMap ℂ (D n) (c k) - a k n)
            + G.q n (a k n - algebraMap ℂ (D n) (c l)) :=
        G.sub_le_sub_add_sub n _ (a k n) _
      have t2 : G.q n (a k n - algebraMap ℂ (D n) (c l))
          ≤ G.q n (a k n - x n) + G.q n (x n - algebraMap ℂ (D n) (c l)) :=
        G.sub_le_sub_add_sub n _ (x n) _
      have t3 : G.q n (x n - algebraMap ℂ (D n) (c l))
          ≤ G.q n (x n - a l n) + G.q n (a l n - algebraMap ℂ (D n) (c l)) :=
        G.sub_le_sub_add_sub n _ (a l n) _
      have e1 : G.q n (algebraMap ℂ (D n) (c k) - algebraMap ℂ (D n) (c l))
          = ‖c k - c l‖ := by
        rw [← map_sub]
        exact G.q_algebraMap n (c k - c l)
      have e2 : G.q n (algebraMap ℂ (D n) (c k) - a k n)
          = G.q n (a k n - algebraMap ℂ (D n) (c k)) := G.sub_comm_eq n _ _
      have e3 : G.q n (a k n - x n) = G.q n (x n - a k n) := G.sub_comm_eq n _ _
      have h4 : G.q n (x n - a k n) < ε / 4 := hK k hk n
      have h5 : G.q n (x n - a l n) < ε / 4 := hK l hl n
      linarith
    have hconst : Tendsto (fun _ : ℕ ↦ ε / 2) atTop (nhds (ε / 2)) :=
      tendsto_const_nhds
    have hsum : Tendsto (fun n ↦ (G.q n (a k n - algebraMap ℂ (D n) (c k))
        + G.q n (a l n - algebraMap ℂ (D n) (c l))) + ε / 2) atTop
        (nhds (ε / 2)) := by
      simpa using ((hc k).add (hc l)).add hconst
    have hle : ‖c k - c l‖ ≤ ε / 2 := ge_of_tendsto' hsum hbound
    calc dist (c k) (c l) = ‖c k - c l‖ := by rw [dist_eq_norm]
      _ ≤ ε / 2 := hle
      _ < ε := by linarith
  obtain ⟨c0, hc0⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [mem_scalarPlusJ_iff_sub]
  refine ⟨c0, ?_⟩
  show Tendsto (fun n ↦ G.q n (x n - algebraMap ℂ (D n) c0)) atTop (nhds 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := hconv (ε / 3) (by linarith)
  have hcdist : ∀ᶠ k in atTop, dist (c k) c0 < ε / 3 :=
    (Metric.tendsto_nhds.mp hc0) (ε / 3) (by linarith)
  obtain ⟨k, hkK, hkd⟩ := ((eventually_ge_atTop K).and hcdist).exists
  have htail : ∀ᶠ n in atTop,
      G.q n (a k n - algebraMap ℂ (D n) (c k)) < ε / 3 :=
    ((Metric.tendsto_nhds.mp (hc k)) (ε / 3) (by linarith)).mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  filter_upwards [htail] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)]
  have t1 : G.q n (x n - algebraMap ℂ (D n) c0)
      ≤ G.q n (x n - a k n) + G.q n (a k n - algebraMap ℂ (D n) c0) :=
    G.sub_le_sub_add_sub n _ (a k n) _
  have t2 : G.q n (a k n - algebraMap ℂ (D n) c0)
      ≤ G.q n (a k n - algebraMap ℂ (D n) (c k))
        + G.q n (algebraMap ℂ (D n) (c k) - algebraMap ℂ (D n) c0) :=
    G.sub_le_sub_add_sub n _ (algebraMap ℂ (D n) (c k)) _
  have e1 : G.q n (algebraMap ℂ (D n) (c k) - algebraMap ℂ (D n) c0)
      = ‖c k - c0‖ := by
    rw [← map_sub]
    exact G.q_algebraMap n (c k - c0)
  have h3 : G.q n (x n - a k n) < ε / 3 := hK k hkK n
  have h4 : ‖c k - c0‖ < ε / 3 := by rwa [dist_eq_norm] at hkd
  linarith

/-! ## (A8) as an equality of sets -/

/-- The `c₀`-sum unitization sits inside `ℂ1 + J`, so the identification of
(A8) really identifies the completion of `A` and not of a smaller algebra. -/
theorem unitizedC0Sum_subset_scalarPlusJ (G : TracialTwoGauge D) :
    unitizedC0Sum D ⊆ scalarPlusJ G := by
  intro x hx
  rw [scalarPlusJ_eq_scalarPlusTwoNull]
  exact unitizedC0Sum_subset_scalarPlusTwoNull G.toUniformTwoGauge hx

/-- **(A8).**  The bounded sequences which are boundedly uniformly
two-approximable from `A = unitization(⊕_s D_s)` are exactly `ℂ1 + J`.

The forward inclusion is the audit's tail truncation (A9); the converse is
`mem_scalarPlusJ_of_uniformTwoLimit` together with `A ⊆ ℂ1 + J`. -/
theorem scalarPlusJ_eq_boundedUniformTwoClosure (G : TracialTwoGauge D) :
    scalarPlusJ G =
      {x : BoundedCStarSequence D |
        IsBoundedUniformTwoApproximable G.toUniformTwoGauge
          (unitizedC0Sum D) x} := by
  ext x
  constructor
  · intro hx
    rw [scalarPlusJ_eq_scalarPlusTwoNull] at hx
    exact scalarPlusTwoNull_subset_boundedUniformTwoApproximable
      G.toUniformTwoGauge hx
  · rintro ⟨a, hmem, -, hconv⟩
    exact mem_scalarPlusJ_of_uniformTwoLimit G
      (fun k ↦ unitizedC0Sum_subset_scalarPlusJ G (hmem k)) hconv

/-- Non-vacuity of the hypotheses of the converse theorem: every element of
`ℂ1 + J` supplies an operator-norm bounded, uniformly two-Cauchy sequence out
of `A`, namely its own scalar truncations. -/
theorem exists_uniformTwoCauchy_scalarTruncations (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D} (hx : x ∈ scalarPlusJ G) :
    ∃ (a : ℕ → BoundedCStarSequence D) (C : ℝ),
      (∀ k, a k ∈ unitizedC0Sum D) ∧ (∀ k, ‖a k‖ ≤ C) ∧
      (∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
        G.q n (a k n - a l n) < ε) ∧
      ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (x n - a k n) < ε := by
  rw [scalarPlusJ_eq_scalarPlusTwoNull] at hx
  obtain ⟨c, hmem, hbdd, hconv⟩ :=
    scalarTruncations_bounded_uniformly_approximate G.toUniformTwoGauge hx
  exact ⟨fun N ↦ scalarTruncation x c N, max ‖x‖ ‖c‖, hmem, hbdd,
    uniformTwoCauchy_of_uniformTwoConvergent G hconv, hconv⟩

/-! ## The finite-rank comparison realizes the completion -/

/-- **The coordinatewise finite-rank step.**  Under the audit's comparison
`‖a‖ ≤ r s · ‖a‖_{2,s}` (with `r s = sqrt (s+1)` for the intended blocks), an
operator-norm bounded, uniformly two-Cauchy sequence converges coordinatewise
in operator norm.  The coordinate limits obey the same bound, so they assemble
into a bounded sequence, and that sequence is the uniform two-limit.

No abstract completion is used: the limit is produced inside `∏_s D_s`. -/
theorem exists_boundedCStarSequence_uniformTwoLimit
    (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (a : ℕ → BoundedCStarSequence D) {C : ℝ} (hC : ∀ k, ‖a k‖ ≤ C)
    (hcauchy : ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
      G.q n (a k n - a l n) < ε) :
    ∃ y : BoundedCStarSequence D,
      (∀ n, Tendsto (fun k ↦ a k n) atTop (nhds (y n))) ∧
      ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (y n - a k n) < ε := by
  -- normalize the comparison constant to be at least one
  have hRpos : ∀ n : ℕ, (0 : ℝ) < max (r n) 1 :=
    fun n ↦ lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hr' : ∀ (n : ℕ) (z : D n), ‖z‖ ≤ max (r n) 1 * G.q n z := fun n z ↦
    (hr n z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (G.nonneg n z))
  -- each coordinate is operator-norm Cauchy
  have hcoordCauchy : ∀ n : ℕ, CauchySeq fun k ↦ a k n := by
    intro n
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hne : max (r n) 1 ≠ 0 := (hRpos n).ne'
    obtain ⟨K, hK⟩ := hcauchy (ε / max (r n) 1) (div_pos hε (hRpos n))
    refine ⟨K, fun k hk l hl ↦ ?_⟩
    have h1 : ‖a k n - a l n‖ ≤ max (r n) 1 * G.q n (a k n - a l n) :=
      hr' n (a k n - a l n)
    have h2 : G.q n (a k n - a l n) < ε / max (r n) 1 := hK k hk l hl n
    have h3 : max (r n) 1 * G.q n (a k n - a l n)
        < max (r n) 1 * (ε / max (r n) 1) :=
      mul_lt_mul_of_pos_left h2 (hRpos n)
    have h4 : max (r n) 1 * (ε / max (r n) 1) = ε := by field_simp
    rw [dist_eq_norm]
    linarith
  have hex : ∀ n : ℕ, ∃ z : D n, Tendsto (fun k ↦ a k n) atTop (nhds z) :=
    fun n ↦ cauchySeq_tendsto_of_complete (hcoordCauchy n)
  choose y hy using hex
  -- the coordinate limits are uniformly bounded
  have hybound : ∀ n : ℕ, ‖y n‖ ≤ C := by
    intro n
    have hnorm : Tendsto (fun k ↦ ‖a k n‖) atTop (nhds ‖y n‖) :=
      (continuous_norm.tendsto (y n)).comp (hy n)
    refine le_of_tendsto hnorm (Eventually.of_forall fun k ↦ ?_)
    exact (boundedCStarSequence_coord_norm_le D (a k) n).trans (hC k)
  have hmem : Memℓp y ∞ := memℓp_infty ⟨C, by
    rintro _ ⟨n, rfl⟩
    exact hybound n⟩
  refine ⟨⟨y, hmem⟩, hy, ?_⟩
  intro ε hε
  obtain ⟨K, hK⟩ := hcauchy (ε / 2) (by linarith)
  refine ⟨K, fun k hk n ↦ ?_⟩
  show G.q n (y n - a k n) < ε
  have hclose : ∀ᶠ l in atTop, ‖y n - a l n‖ < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp (hy n)) (ε / 2) (by linarith)
    filter_upwards [h] with l hl
    have hd : dist (a l n) (y n) < ε / 2 := hl
    rwa [dist_comm, dist_eq_norm] at hd
  obtain ⟨l, hlK, hl⟩ := ((eventually_ge_atTop K).and hclose).exists
  have t1 : G.q n (y n - a k n)
      ≤ G.q n (y n - a l n) + G.q n (a l n - a k n) :=
    G.sub_le_sub_add_sub n _ (a l n) _
  have t2 : G.q n (y n - a l n) ≤ ‖y n - a l n‖ := G.le_norm n _
  have t3 : G.q n (a l n - a k n) < ε / 2 := hK l hlK k hk n
  linarith

/-- **The converse half of (A8), assembled.**  A uniformly bounded, uniformly
two-Cauchy sequence drawn from `A = unitization(⊕_s D_s)` has a limit inside
the bounded product, and that limit lies in `ℂ1 + J`. -/
theorem exists_mem_scalarPlusJ_of_uniformTwoCauchy
    (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (a : ℕ → BoundedCStarSequence D) (hA : ∀ k, a k ∈ unitizedC0Sum D)
    {C : ℝ} (hC : ∀ k, ‖a k‖ ≤ C)
    (hcauchy : ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
      G.q n (a k n - a l n) < ε) :
    ∃ y : BoundedCStarSequence D,
      y ∈ scalarPlusJ G ∧
      (∀ n, Tendsto (fun k ↦ a k n) atTop (nhds (y n))) ∧
      ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (y n - a k n) < ε := by
  obtain ⟨y, hycoord, hyconv⟩ :=
    exists_boundedCStarSequence_uniformTwoLimit G hr a hC hcauchy
  refine ⟨y, ?_, hycoord, hyconv⟩
  exact mem_scalarPlusJ_of_uniformTwoLimit G
    (fun k ↦ unitizedC0Sum_subset_scalarPlusJ G (hA k)) hyconv

/-- Section 4 of the audit in one statement.  `ℂ1 + J` is a norm-closed star
subalgebra of the bounded product; it contains `A = unitization(⊕_s D_s)`; it
is exactly the bounded uniform two-closure of `A`; and under the coordinatewise
finite-rank comparison every uniformly bounded uniformly two-Cauchy sequence
from `A` has its limit there. -/
theorem uniformTracialCompletion_identification
    (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r) :
    IsClosed (scalarPlusJ G) ∧
    (scalarPlusJSubalgebra G : Set (BoundedCStarSequence D)) = scalarPlusJ G ∧
    unitizedC0Sum D ⊆ scalarPlusJ G ∧
    scalarPlusJ G =
      {x : BoundedCStarSequence D |
        IsBoundedUniformTwoApproximable G.toUniformTwoGauge
          (unitizedC0Sum D) x} ∧
    ∀ (a : ℕ → BoundedCStarSequence D), (∀ k, a k ∈ unitizedC0Sum D) →
      ∀ C : ℝ, (∀ k, ‖a k‖ ≤ C) →
      (∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
        G.q n (a k n - a l n) < ε) →
      ∃ y : BoundedCStarSequence D, y ∈ scalarPlusJ G ∧
        ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (y n - a k n) < ε :=
  ⟨isClosed_scalarPlusJ G, coe_scalarPlusJSubalgebra G,
    unitizedC0Sum_subset_scalarPlusJ G,
    scalarPlusJ_eq_boundedUniformTwoClosure G,
    fun a hA C hC hcauchy ↦ by
      obtain ⟨y, hy, -, hyconv⟩ :=
        exists_mem_scalarPlusJ_of_uniformTwoCauchy G hr a hA hC hcauchy
      exact ⟨y, hy, hyconv⟩⟩

end

end UniformTracialCompletionIdentification
end GroupApproximation
