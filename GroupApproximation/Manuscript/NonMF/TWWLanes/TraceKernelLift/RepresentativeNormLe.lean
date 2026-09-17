import GroupApproximation.Analysis.TracialMatrixQuotientUnitBall
import GroupApproximation.Analysis.ShulmanTraceFactorization
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.RadialTruncation
import GroupApproximation.Meta.AxiomGuard

/-!
# The quotient norm of the tracial matrix ultraproduct is attained

Lane `nm-tww-07`.  For a free ultrafilter `ω`, every class `x` in the tracial matrix
quotient `∏_ω M_{k_n} / (‖·‖₂-null)` has a representative `c` with `‖c‖ ≤ ‖x‖`, where
`‖c‖` is the ℓ∞ operator norm.  The quotient norm is only an infimum, so this needs an
argument.

Choose representatives `a_k` with `‖a_k‖ < ‖x‖ + 1/(k+1)`.  Every difference `a_k − a_0`
is `‖·‖₂`-null.  At coordinate `n`, take the largest `k(n) ≤ n` such that the coordinate
distances `‖(a_i − a_0)_n‖₂` are below `1/(i+1)` for all `i ≤ k(n)`.  Then radially
truncate `(a_{k(n)})_n` to radius `‖x‖`.  The truncation moves the coordinate by at most
`1/(k(n)+1)` in operator norm, hence also in `‖·‖₂`, and `k(n) → ∞` along `ω`.  So the
truncated sequence differs from `a_0` by a `‖·‖₂`-null sequence.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift

open Filter Matrix TracialUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- **The tracial quotient norm is attained by a representative.** -/
theorem exists_rep_norm_le (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ∃ c : ModelBoundedSequence X,
      tracialMatrixQuotientMk X (ω : Filter ℕ) c = x ∧ ‖c‖ ≤ ‖x‖ := by
  classical
  choose a ha using fun k : ℕ ↦
    tracialQuot_exists_rep_norm_lt (X := X) (l := (ω : Filter ℕ)) x
      (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  have hmk : ∀ k, tracialMatrixQuotientMk X (ω : Filter ℕ) (a k) = x := fun k ↦ (ha k).1
  have hnull : ∀ i, IsHilbertSchmidtNull X (ω : Filter ℕ) (a i - a 0) := fun i ↦
    (tracialMatrixQuotientMk_eq_zero_iff X (ω : Filter ℕ) (a i - a 0)).mp
      (by rw [map_sub, hmk i, hmk 0, sub_self])
  -- the `ω`-large conditions
  let B : ℕ → ℕ → Prop := fun i n ↦ hsNorm (X n) ((a i - a 0) n) < 1 / ((i : ℝ) + 1)
  let P : ℕ → ℕ → Prop := fun n j ↦ ∀ i ∈ Finset.range (j + 1), B i n
  have hPev : ∀ j, ∀ᶠ n in (ω : Filter ℕ), P n j := fun j ↦
    (Filter.eventually_all_finset (Finset.range (j + 1))).mpr fun i _ ↦
      eventually_lt_of_tendsto_zero
        (show Tendsto (fun n ↦ hsNorm (X n) ((a i - a 0) n)) (ω : Filter ℕ) (nhds 0) from
          hnull i) (by positivity)
  have hB0 : ∀ n, B 0 n := by
    intro n
    show hsNorm (X n) ((a 0 - a 0) n) < 1 / (((0 : ℕ) : ℝ) + 1)
    rw [sub_self, ShulmanTrace.modelSeq_zero_apply, TracialUltraproduct.hsNorm_zero]
    norm_num
  -- the diagonal index
  let k : ℕ → ℕ := fun n ↦ Nat.findGreatest (P n) n
  have hk_P : ∀ n, P n (k n) := fun n ↦
    Nat.findGreatest_spec (P := P n) (Nat.zero_le n) (fun i hi ↦ by
      have hi0 : i = 0 := by
        have h := Finset.mem_range.mp hi
        omega
      rw [hi0]
      exact hB0 n)
  have hk_spec : ∀ n, B (k n) n := fun n ↦
    hk_P n (k n) (Finset.mem_range.mpr (Nat.lt_succ_self _))
  have hk_large : ∀ J, ∀ᶠ n in (ω : Filter ℕ), J ≤ k n := by
    intro J
    have hge : ∀ᶠ n in (ω : Filter ℕ), J ≤ n :=
      TracialUnitBall.le_atTop_of_le_cofinite ω hω (Filter.eventually_ge_atTop J)
    filter_upwards [hPev J, hge] with n hP hJ
    exact Nat.le_findGreatest (P := P n) hJ hP
  -- the truncated diagonal representative
  have hxn : 0 ≤ ‖x‖ := norm_nonneg x
  let c0 : ∀ n, Matrix (X n) (X n) ℂ := fun n ↦ radialTrunc ‖x‖ ((a (k n)) n)
  have hc0 : ∀ n, ‖c0 n‖ ≤ ‖x‖ := fun n ↦ norm_radialTrunc_le hxn _
  let c : ModelBoundedSequence X := ShulmanTrace.boundedSeqOfBound c0 hc0
  have hdefect : ∀ n, hsNorm (X n) ((c - a 0) n) ≤ 2 / ((k n : ℝ) + 1) := by
    intro n
    have hnorm : ‖(a (k n)) n‖ ≤ ‖x‖ + 1 / ((k n : ℝ) + 1) :=
      (boundedMatrixSequence_coord_norm_le (fun n ↦ X n) (a (k n)) n).trans (ha (k n)).2.le
    have htr : ‖c0 n - (a (k n)) n‖ ≤ 1 / ((k n : ℝ) + 1) :=
      norm_radialTrunc_sub_le hxn (by positivity) _ hnorm
    have hsplit : (c - a 0) n = (c0 n - (a (k n)) n) + (a (k n) - a 0) n := by
      rw [ShulmanTrace.modelSeq_sub_apply, ShulmanTrace.modelSeq_sub_apply]
      exact (sub_add_sub_cancel (c0 n) ((a (k n)) n) ((a 0) n)).symm
    rw [hsplit]
    calc hsNorm (X n) ((c0 n - (a (k n)) n) + (a (k n) - a 0) n)
        ≤ hsNorm (X n) (c0 n - (a (k n)) n) + hsNorm (X n) ((a (k n) - a 0) n) :=
          Manuscript.OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le (X n)
            Fintype.card_pos _ _
      _ ≤ 1 / ((k n : ℝ) + 1) + 1 / ((k n : ℝ) + 1) :=
          add_le_add ((PrelimNotation.hsNorm_le_l2_opNorm (X n) _).trans htr)
            (le_of_lt (hk_spec n))
      _ = 2 / ((k n : ℝ) + 1) := by ring
  have hcnull : IsHilbertSchmidtNull X (ω : Filter ℕ) (c - a 0) := by
    show Tendsto (fun n ↦ hsNorm (X n) ((c - a 0) n)) (ω : Filter ℕ) (nhds 0)
    refine tendsto_zero_of_forall_eventually_lt (fun n ↦ hsNorm_nonneg _ _) fun ε hε ↦ ?_
    obtain ⟨J, hJ⟩ := exists_nat_gt (2 / ε)
    filter_upwards [hk_large J] with n hn
    have hJpos : (0 : ℝ) < (J : ℝ) + 1 := by positivity
    have hle : (J : ℝ) + 1 ≤ (k n : ℝ) + 1 := by
      have h : (J : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hn
      linarith
    calc hsNorm (X n) ((c - a 0) n) ≤ 2 / ((k n : ℝ) + 1) := hdefect n
      _ ≤ 2 / ((J : ℝ) + 1) := div_le_div_of_nonneg_left (by norm_num) hJpos hle
      _ < ε := by
        rw [div_lt_iff₀ hJpos]
        have h := (div_lt_iff₀ hε).mp hJ
        nlinarith
  refine ⟨c, ?_, lp.norm_le_of_forall_le hxn fun n ↦ hc0 n⟩
  rw [ShulmanTrace.mk_eq_mk_of_isHilbertSchmidtNull hcnull, hmk 0]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.exists_rep_norm_le

end

end GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift
