import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbQuasicentralStep
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Quasicentral approximate units, step 2: the schedule and the bookkeeping

Lane TWWSch3c2C1, work order WO-TWWSch-3c2-C1.  Manuscript `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378); the construction follows Arveson 1977, Thm. 1,
Kasparov 1980, §3 and Higson--Roe, *Analytic K-homology*, 3.2.

The quasicentral unit is built by iterating `quasiUnit_exists_step`.  This file provides the
pieces that are not about C⋆-algebras:

* `quasiUnit_exists_seq`: dependent choice for a step relation depending on `n`;
* the tolerance schedule `quasiUnitGap ε n = min(ε 0, …, ε n, 1) · (1/2)^(n+2)`: positive,
  strictly decreasing, at most `ε n / 4` and tending to `0`;
* the domination ratios `quasiUnitRatio ε n = (1 - u n) / (1 - u (n+1)) ∈ [0, 1)`, chosen so
  that the rescaled elements `(1 - u (n+1)) • g (n+1)` are increasing;
* `quasiUnit_norm_smul_sub_le`, the cost of a rescaling, and `quasiUnit_tendsto_of_dense`,
  which extends convergence from a dense sequence along uniformly contractive maps.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter Topology

noncomputable section

/-- **Dependent choice** for a step relation `R n` preserving `p`. -/
theorem quasiUnit_exists_seq {α : Type*} (p : α → Prop) (x0 : α) (h0 : p x0)
    (R : ℕ → α → α → Prop) (hstep : ∀ n x, p x → ∃ y, p y ∧ R n x y) :
    ∃ g : ℕ → α, (∀ n, p (g n)) ∧ ∀ n, R n (g n) (g (n + 1)) := by
  choose f hf using hstep
  let G : ℕ → {x // p x} := fun n ↦
    Nat.rec (motive := fun _ ↦ {x // p x}) ⟨x0, h0⟩
      (fun k z ↦ ⟨f k z.1 z.2, (hf k z.1 z.2).1⟩) n
  refine ⟨fun n ↦ (G n).1, fun n ↦ (G n).2, fun n ↦ ?_⟩
  exact (hf n (G n).1 (G n).2).2

/-- Running minimum of `ε`, capped at `1`. -/
def quasiUnitMin (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => min (ε 0) 1
  | n + 1 => min (quasiUnitMin ε n) (ε (n + 1))

theorem quasiUnitMin_zero (ε : ℕ → ℝ) : quasiUnitMin ε 0 = min (ε 0) 1 := rfl

theorem quasiUnitMin_succ (ε : ℕ → ℝ) (n : ℕ) :
    quasiUnitMin ε (n + 1) = min (quasiUnitMin ε n) (ε (n + 1)) := rfl

theorem quasiUnitMin_pos {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (n : ℕ) : 0 < quasiUnitMin ε n := by
  induction n with
  | zero => rw [quasiUnitMin_zero]; exact lt_min (hε 0) one_pos
  | succ n ih => rw [quasiUnitMin_succ]; exact lt_min ih (hε (n + 1))

theorem quasiUnitMin_le (ε : ℕ → ℝ) (n : ℕ) : quasiUnitMin ε n ≤ ε n := by
  cases n with
  | zero => rw [quasiUnitMin_zero]; exact min_le_left _ _
  | succ n => rw [quasiUnitMin_succ]; exact min_le_right _ _

theorem quasiUnitMin_le_one (ε : ℕ → ℝ) (n : ℕ) : quasiUnitMin ε n ≤ 1 := by
  induction n with
  | zero => rw [quasiUnitMin_zero]; exact min_le_right _ _
  | succ n ih => rw [quasiUnitMin_succ]; exact (min_le_left _ _).trans ih

/-- The tolerance schedule `u n`. -/
def quasiUnitGap (ε : ℕ → ℝ) (n : ℕ) : ℝ := quasiUnitMin ε n * (1 / 2) ^ (n + 2)

theorem quasiUnit_half_pow_le (n : ℕ) : ((1 : ℝ) / 2) ^ (n + 2) ≤ 1 / 4 := by
  have h : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc ((1 : ℝ) / 2) ^ (n + 2) = (1 / 2) ^ n * (1 / 4) := by ring
    _ ≤ 1 * (1 / 4) := mul_le_mul_of_nonneg_right h (by norm_num)
    _ = 1 / 4 := one_mul _

theorem quasiUnitGap_pos {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (n : ℕ) : 0 < quasiUnitGap ε n :=
  mul_pos (quasiUnitMin_pos hε n) (pow_pos (by norm_num) _)

theorem quasiUnitGap_le_pow (ε : ℕ → ℝ) (n : ℕ) :
    quasiUnitGap ε n ≤ ((1 : ℝ) / 2) ^ (n + 2) := by
  have h := mul_le_mul_of_nonneg_right (quasiUnitMin_le_one ε n)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (n + 2))
  rw [one_mul] at h
  exact h

theorem quasiUnitGap_le_quarter (ε : ℕ → ℝ) (n : ℕ) : quasiUnitGap ε n ≤ 1 / 4 :=
  (quasiUnitGap_le_pow ε n).trans (quasiUnit_half_pow_le n)

theorem quasiUnitGap_le {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (n : ℕ) :
    quasiUnitGap ε n ≤ ε n / 4 := by
  have hm0 := (quasiUnitMin_pos hε n).le
  have hm := quasiUnitMin_le ε n
  calc quasiUnitGap ε n ≤ quasiUnitMin ε n * (1 / 4) :=
        mul_le_mul_of_nonneg_left (quasiUnit_half_pow_le n) hm0
    _ ≤ ε n / 4 := by linarith

theorem quasiUnitGap_succ_lt {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (n : ℕ) :
    quasiUnitGap ε (n + 1) < quasiUnitGap ε n := by
  have hq : (0 : ℝ) < (1 / 2) ^ (n + 2) := pow_pos (by norm_num) _
  have hpow : ((1 : ℝ) / 2) ^ (n + 1 + 2) = (1 / 2) ^ (n + 2) * (1 / 2) := by ring
  have hm' := quasiUnitMin_pos hε (n + 1)
  have hmm : quasiUnitMin ε (n + 1) ≤ quasiUnitMin ε n := by
    rw [quasiUnitMin_succ]
    exact min_le_left _ _
  have h1 := mul_le_mul_of_nonneg_right hmm hq.le
  have h2 := mul_pos hm' hq
  unfold quasiUnitGap
  rw [hpow]
  linarith

theorem quasiUnitGap_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) :
    Tendsto (quasiUnitGap ε) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (n + 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 2)
  exact squeeze_zero (fun n ↦ (quasiUnitGap_pos hε n).le) (quasiUnitGap_le_pow ε) hg

/-- The domination ratio `(1 - u n) / (1 - u (n+1))`. -/
def quasiUnitRatio (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - quasiUnitGap ε n) / (1 - quasiUnitGap ε (n + 1))

theorem quasiUnitRatio_nonneg (ε : ℕ → ℝ) (n : ℕ) : 0 ≤ quasiUnitRatio ε n := by
  have h1 := quasiUnitGap_le_quarter ε n
  have h2 := quasiUnitGap_le_quarter ε (n + 1)
  unfold quasiUnitRatio
  exact div_nonneg (by linarith) (by linarith)

theorem quasiUnitRatio_lt_one {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (n : ℕ) :
    quasiUnitRatio ε n < 1 := by
  have h2 := quasiUnitGap_le_quarter ε (n + 1)
  have h3 := quasiUnitGap_succ_lt hε n
  unfold quasiUnitRatio
  exact (div_lt_one (by linarith)).2 (by linarith)

theorem quasiUnitRatio_mul (ε : ℕ → ℝ) (n : ℕ) :
    (1 - quasiUnitGap ε (n + 1)) * quasiUnitRatio ε n = 1 - quasiUnitGap ε n := by
  have h2 := quasiUnitGap_le_quarter ε (n + 1)
  have hne : (1 - quasiUnitGap ε (n + 1)) ≠ 0 := by
    intro h
    linarith
  unfold quasiUnitRatio
  exact mul_div_cancel₀ _ hne

/-- **The cost of a rescaling**: for `0 ≤ s ≤ 1`, `‖s X - Y‖ ≤ ‖X - Y‖ + (1 - s) ‖Y‖`. -/
theorem quasiUnit_norm_smul_sub_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (X Y : E) :
    ‖s • X - Y‖ ≤ ‖X - Y‖ + (1 - s) * ‖Y‖ := by
  have hid : s • X - Y = s • (X - Y) - (1 - s) • Y := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hid]
  calc ‖s • (X - Y) - (1 - s) • Y‖ ≤ ‖s • (X - Y)‖ + ‖(1 - s) • Y‖ := norm_sub_le _ _
    _ = s * ‖X - Y‖ + (1 - s) * ‖Y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs0,
          Real.norm_of_nonneg (sub_nonneg.2 hs1)]
    _ ≤ ‖X - Y‖ + (1 - s) * ‖Y‖ := by
        have h := mul_le_mul_of_nonneg_right hs1 (norm_nonneg (X - Y))
        linarith

/-- **Density**: convergence `T n x → x` along uniformly contractive maps extends from a dense
sequence to every point. -/
theorem quasiUnit_tendsto_of_dense {E : Type*} [SeminormedAddCommGroup E] (T : ℕ → E → E)
    (hT : ∀ n x y, ‖T n x - T n y‖ ≤ ‖x - y‖) (K : ℕ → E) (hK : DenseRange K)
    (hKlim : ∀ m, Tendsto (fun n ↦ T n (K m)) atTop (𝓝 (K m))) (k : E) :
    Tendsto (fun n ↦ T n k) atTop (𝓝 k) := by
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨m, hm⟩ := Metric.denseRange_iff.1 hK k (r / 3) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hKlim m) (r / 3) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 : dist (T n (K m)) (K m) < r / 3 := hN n hn
  have h2 := hT n k (K m)
  have hm' : dist k (K m) < r / 3 := hm
  show dist (T n k) k < r
  rw [dist_eq_norm] at h1 hm' ⊢
  calc ‖T n k - k‖ = ‖(T n k - T n (K m)) + (T n (K m) - K m) + (K m - k)‖ := by
        congr 1
        abel
    _ ≤ ‖T n k - T n (K m)‖ + ‖T n (K m) - K m‖ + ‖K m - k‖ := norm_add₃_le
    _ < r := by
        rw [norm_sub_rev (K m) k]
        linarith

end

end TWWSchafhauser
end Full
end GroupApproximation
