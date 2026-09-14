import GroupApproximation.Analysis.SoficHyperlinearTrace
import GroupApproximation.Analysis.TracialUltraproductCStar
import GroupApproximation.Manuscript.OneSidedMFRadical.HilbertSchmidtOperatorAction
import Mathlib.Analysis.SpecificLimits.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Bounded `‖·‖₂`-Cauchy sequences converge in the tracial matrix ultraproduct

Infrastructure of lane `oa-mcduff` (absorbed from oa-ozawa71) for `simple_kazhdan_sofic_group.tex` at
origin/main 8b36733d7, "Brown's formulation", tex 277–279 (census row `fc6e6384121b`): "So `L(G)`
embeds in `𝓡^ω`".  The extension of a trace-preserving map from `C*(G)` to `L(G)` takes `‖·‖₂`-limits
of uniformly bounded sequences, and this module shows they exist in `∏_ω M_k`.

* `twoNormSq ω x = Re tr_ω (x⋆x)`, and `twoNormSq_mk`: on a lift it is `lim_ω ‖aₙ‖₂²`.
* `seqHSLimit_add_le`: `‖a + b‖₂² ≤ 2‖a‖₂² + 2‖b‖₂²`.
* `hsNorm_sub_le_sum`: the telescoping triangle inequality for the normalized Hilbert–Schmidt norm.
* `exists_tendsto_twoNormSq_of_cauchy`: for a free ultrafilter, a `‖·‖₂`-Cauchy sequence of norm at most
  `C` has a `‖·‖₂`-limit of norm at most `C + 1`.  Choose lifts of norm below `C + 1`, a fast subsequence
  with consecutive distances below `4^{-j}`, the `ω`-large sets `A_j` where the first `j` coordinate
  distances are below `4^{-i}`, and at coordinate `n` the lift with the largest index `j ≤ n` such
  that `n ∈ A_j`.
-/

namespace GroupApproximation
namespace TracialUnitBall

open Filter Matrix TracialUltraproduct ShulmanTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## A fast subsequence of indices -/

/-- A strictly increasing sequence of indices dominating `K`. -/
def fastIndex (K : ℕ → ℕ) : ℕ → ℕ
  | 0 => K 0
  | j + 1 => max (fastIndex K j) (K (j + 1)) + 1

theorem le_fastIndex (K : ℕ → ℕ) : ∀ j, K j ≤ fastIndex K j
  | 0 => le_rfl
  | j + 1 => by
    show K (j + 1) ≤ max (fastIndex K j) (K (j + 1)) + 1
    exact le_trans (le_max_right _ _) (Nat.le_succ _)

theorem fastIndex_le_succ (K : ℕ → ℕ) (j : ℕ) : fastIndex K j ≤ fastIndex K (j + 1) := by
  show fastIndex K j ≤ max (fastIndex K j) (K (j + 1)) + 1
  exact le_trans (le_max_left _ _) (Nat.le_succ _)

theorem fastIndex_mono (K : ℕ → ℕ) : Monotone (fastIndex K) :=
  monotone_nat_of_le_succ (fastIndex_le_succ K)

theorem self_le_fastIndex (K : ℕ → ℕ) : ∀ j, j ≤ fastIndex K j
  | 0 => Nat.zero_le _
  | j + 1 => by
    show j + 1 ≤ max (fastIndex K j) (K (j + 1)) + 1
    exact Nat.succ_le_succ (le_trans (self_le_fastIndex K j) (le_max_left _ _))

/-! ## The telescoping triangle inequality -/

theorem hsNorm_sub_le_sum (Y : FiniteModel) (hY : 0 < Fintype.card Y) (f : ℕ → Matrix Y Y ℂ)
    (J : ℕ) : ∀ k : ℕ, hsNorm Y (f J - f (J + k)) ≤
      ∑ i ∈ Finset.range k, hsNorm Y (f (J + i) - f (J + i + 1))
  | 0 => by
    simp only [add_zero, sub_self, Finset.range_zero, Finset.sum_empty]
    rw [hsNorm, TracialUltraproduct.hsNormSq_zero, Real.sqrt_zero]
  | k + 1 => by
    rw [Finset.sum_range_succ]
    calc hsNorm Y (f J - f (J + (k + 1)))
        = hsNorm Y ((f J - f (J + k)) + (f (J + k) - f (J + k + 1))) := by
          rw [sub_add_sub_cancel]
          rfl
      _ ≤ hsNorm Y (f J - f (J + k)) + hsNorm Y (f (J + k) - f (J + k + 1)) :=
          Manuscript.OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le Y hY _ _
      _ ≤ (∑ i ∈ Finset.range k, hsNorm Y (f (J + i) - f (J + i + 1))) +
            hsNorm Y (f (J + k) - f (J + k + 1)) := by
          gcongr
          exact hsNorm_sub_le_sum Y hY f J k

/-! ## The `‖·‖₂`-norm on the ultraproduct -/

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)

/-- The squared `‖·‖₂`-norm `Re tr_ω (x⋆x)` on the tracial ultraproduct. -/
def twoNormSq (x : TracialMatrixQuotient X (ω : Filter ℕ)) : ℝ :=
  (ultratrace X ω (star x * x)).re

theorem twoNormSq_mk (a : ModelBoundedSequence X) :
    twoNormSq ω (tracialMatrixQuotientMk X (ω : Filter ℕ) a) = seqHSLimit X ω a := by
  unfold twoNormSq
  rw [ultratrace_star_mul_self_eq_ofReal, Complex.ofReal_re]

omit [∀ n, Nonempty (X n)] in
theorem seqHSLimit_add_le (a b : ModelBoundedSequence X) :
    seqHSLimit X ω (a + b) ≤ 2 * seqHSLimit X ω a + 2 * seqHSLimit X ω b :=
  le_of_tendsto_of_tendsto' (tendsto_seqHSLimit X ω (a + b))
    (((tendsto_seqHSLimit X ω a).const_mul 2).add ((tendsto_seqHSLimit X ω b).const_mul 2))
    fun n ↦ hsNormSq_add_le (X n) (a n) (b n)

theorem le_atTop_of_le_cofinite (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    (ω : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  exact hω

/-! ## Completeness of bounded sets -/

/-- **A `‖·‖₂`-Cauchy sequence of norm at most `C` has a `‖·‖₂`-limit of norm at most `C + 1`.** -/
theorem exists_tendsto_twoNormSq_of_cauchy (hω : (ω : Filter ℕ) ≤ Filter.cofinite) {C : ℝ}
    (x : ℕ → TracialMatrixQuotient X (ω : Filter ℕ)) (hbound : ∀ k, ‖x k‖ ≤ C)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, twoNormSq ω (x k - x l) < ε) :
    ∃ y : TracialMatrixQuotient X (ω : Filter ℕ), ‖y‖ ≤ C + 1 ∧
      Tendsto (fun k ↦ twoNormSq ω (x k - y)) atTop (nhds 0) := by
  classical
  choose a ha using fun k ↦
    tracialQuot_exists_rep_norm_lt (X := X) (l := (ω : Filter ℕ)) (x k) one_pos
  have hmk : ∀ k, tracialMatrixQuotientMk X (ω : Filter ℕ) (a k) = x k := fun k ↦ (ha k).1
  have hna : ∀ k, ‖a k‖ ≤ C + 1 := fun k ↦ by linarith [(ha k).2, hbound k]
  have hdiff : ∀ k l, twoNormSq ω (x k - x l) = seqHSLimit X ω (a k - a l) := by
    intro k l
    rw [← hmk k, ← hmk l, ← map_sub, twoNormSq_mk]
  choose K hK using fun j : ℕ ↦ hcauchy ((1 / 4 : ℝ) ^ j) (by positivity)
  have hstep : ∀ i, seqHSLimit X ω (a (fastIndex K i) - a (fastIndex K (i + 1))) <
      (1 / 4 : ℝ) ^ i := by
    intro i
    rw [← hdiff]
    exact hK i (fastIndex K i) (le_fastIndex K i) (fastIndex K (i + 1))
      (le_trans (le_fastIndex K i) (fastIndex_mono K (Nat.le_succ i)))
  -- the `ω`-large sets `A_j`
  let A : ℕ → Set ℕ := fun j ↦
    {n | ∀ i ∈ Finset.range j,
      hsNormSq (X n) ((a (fastIndex K i) - a (fastIndex K (i + 1))) n) < (1 / 4 : ℝ) ^ i}
  have hA : ∀ j, ∀ᶠ n in (ω : Filter ℕ), n ∈ A j := by
    intro j
    exact (Filter.eventually_all_finset (Finset.range j)).mpr fun i _ ↦
      UltrafilterLimit.eventually_lt_of_ulim_lt (exists_tendsto_hsNormSq X ω _) (hstep i)
  -- the diagonal index
  let jn : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun j ↦ n ∈ A j) n
  have hjn_spec : ∀ n, n ∈ A (jn n) := fun n ↦
    Nat.findGreatest_spec (P := fun j ↦ n ∈ A j) (Nat.zero_le n)
      (fun i hi ↦ absurd (Finset.mem_range.mp hi) (Nat.not_lt_zero i))
  have hjn_le : ∀ J n, J ≤ n → n ∈ A J → J ≤ jn n := fun J n hJ hn ↦
    Nat.le_findGreatest (P := fun j ↦ n ∈ A j) hJ hn
  have hbn : ∀ n, ‖(a (fastIndex K (jn n))) n‖ ≤ C + 1 := fun n ↦
    (boundedMatrixSequence_coord_norm_le (fun n ↦ X n) (a (fastIndex K (jn n))) n).trans (hna _)
  let b : ModelBoundedSequence X := boundedSeqOfBound (fun n ↦ (a (fastIndex K (jn n))) n) hbn
  have hC1 : 0 ≤ C + 1 := by linarith [norm_nonneg (x 0), hbound 0]
  -- the tail estimate
  have htail : ∀ J, seqHSLimit X ω (a (fastIndex K J) - b) ≤ 4 * (1 / 4 : ℝ) ^ J := by
    intro J
    show UltrafilterLimit.ulim ω (fun n ↦ hsNormSq (X n) ((a (fastIndex K J) - b) n)) ≤ _
    refine UltrafilterLimit.ulim_le (exists_tendsto_hsNormSq X ω _) ?_
    have hge : ∀ᶠ n in (ω : Filter ℕ), J ≤ n :=
      le_atTop_of_le_cofinite ω hω (Filter.eventually_ge_atTop J)
    filter_upwards [hA J, hge] with n hnA hJn
    have hJ : J ≤ jn n := hjn_le J n hJn hnA
    have hspec := hjn_spec n
    have hk : J + (jn n - J) = jn n := Nat.add_sub_cancel' hJ
    have htel := hsNorm_sub_le_sum (X n) Fintype.card_pos (fun i ↦ (a (fastIndex K i)) n) J
      (jn n - J)
    rw [hk] at htel
    have hterm : ∀ i ∈ Finset.range (jn n - J),
        hsNorm (X n) ((a (fastIndex K (J + i))) n - (a (fastIndex K (J + i + 1))) n) ≤
          (1 / 2 : ℝ) ^ J * (1 / 2 : ℝ) ^ i := by
      intro i hi
      have hi' : J + i ∈ Finset.range (jn n) := by
        rw [Finset.mem_range] at hi ⊢
        omega
      have hsq := hspec (J + i) hi'
      have hq : ((1 / 2 : ℝ) ^ (J + i)) ^ 2 = (1 / 4 : ℝ) ^ (J + i) := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have h2 : hsNorm (X n) ((a (fastIndex K (J + i))) n - (a (fastIndex K (J + i + 1))) n) ^ 2 <
          ((1 / 2 : ℝ) ^ (J + i)) ^ 2 := by
        rw [TracialUltraproduct.sq_hsNorm, hq]
        exact hsq
      have h3 := (sq_lt_sq₀ (hsNorm_nonneg _ _) (by positivity)).mp h2
      rw [pow_add] at h3
      exact h3.le
    have hsum : ∑ i ∈ Finset.range (jn n - J),
        hsNorm (X n) ((a (fastIndex K (J + i))) n - (a (fastIndex K (J + i + 1))) n) ≤
          2 * (1 / 2 : ℝ) ^ J := by
      calc ∑ i ∈ Finset.range (jn n - J),
            hsNorm (X n) ((a (fastIndex K (J + i))) n - (a (fastIndex K (J + i + 1))) n)
          ≤ ∑ i ∈ Finset.range (jn n - J), (1 / 2 : ℝ) ^ J * (1 / 2 : ℝ) ^ i :=
            Finset.sum_le_sum hterm
        _ = (1 / 2 : ℝ) ^ J * ∑ i ∈ Finset.range (jn n - J), (1 / 2 : ℝ) ^ i := by
            rw [Finset.mul_sum]
        _ ≤ (1 / 2 : ℝ) ^ J * 2 := by
            gcongr
            exact sum_geometric_two_le _
        _ = 2 * (1 / 2 : ℝ) ^ J := mul_comm _ _
    have hnorm : hsNorm (X n) ((a (fastIndex K J)) n - (a (fastIndex K (jn n))) n) ≤
        2 * (1 / 2 : ℝ) ^ J :=
      htel.trans hsum
    change hsNormSq (X n) ((a (fastIndex K J)) n - (a (fastIndex K (jn n))) n) ≤ 4 * (1 / 4 : ℝ) ^ J
    rw [← TracialUltraproduct.sq_hsNorm]
    calc hsNorm (X n) ((a (fastIndex K J)) n - (a (fastIndex K (jn n))) n) ^ 2
        ≤ (2 * (1 / 2 : ℝ) ^ J) ^ 2 := pow_le_pow_left₀ (hsNorm_nonneg _ _) hnorm 2
      _ = 4 * (1 / 4 : ℝ) ^ J := by
        rw [mul_pow, ← pow_mul, mul_comm J 2, pow_mul]
        norm_num
  refine ⟨tracialMatrixQuotientMk X (ω : Filter ℕ) b,
    (tracialQuot_norm_mk_le (X := X) (l := (ω : Filter ℕ)) b).trans
      (lp.norm_le_of_forall_le hC1 fun n ↦ hbn n), ?_⟩
  refine tendsto_zero_of_forall_eventually_lt (fun k ↦ ?_) fun ε hε ↦ ?_
  · rw [← hmk k, ← map_sub, twoNormSq_mk]
    exact seqHSLimit_nonneg X ω _
  · obtain ⟨K', hK'⟩ := hcauchy (ε / 4) (by positivity)
    obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 16 by positivity)
      (show (1 / 4 : ℝ) < 1 by norm_num)
    refine Filter.eventually_atTop.mpr ⟨K', fun k hk ↦ ?_⟩
    have hmJ : K' ≤ fastIndex K (max K' J₀) :=
      le_trans (le_max_left _ _) (self_le_fastIndex K _)
    have h1 := hK' k hk (fastIndex K (max K' J₀)) hmJ
    have h2 := htail (max K' J₀)
    have hpow : (1 / 4 : ℝ) ^ (max K' J₀) ≤ (1 / 4 : ℝ) ^ J₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    have hsplit : twoNormSq ω (x k - tracialMatrixQuotientMk X (ω : Filter ℕ) b) ≤
        2 * twoNormSq ω (x k - x (fastIndex K (max K' J₀))) +
          2 * seqHSLimit X ω (a (fastIndex K (max K' J₀)) - b) := by
      rw [hdiff, ← hmk k, ← map_sub, twoNormSq_mk]
      have h := seqHSLimit_add_le ω (a k - a (fastIndex K (max K' J₀)))
        (a (fastIndex K (max K' J₀)) - b)
      rwa [sub_add_sub_cancel] at h
    linarith

end

end TracialUnitBall
end GroupApproximation

#audit_axioms GroupApproximation.TracialUnitBall.exists_tendsto_twoNormSq_of_cauchy
