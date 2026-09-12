import GroupApproximation.Analysis.VoiculescuStageVector

/-!
# The tolerance schedule the recursion runs on

The recursion needs a sequence of tolerances `εⱼ` fixed *in advance*, with three
properties: positive, decreasing, and small enough that the modulus turns the
piece commutator into `‖[dⱼ, S_k]‖ < 2⁻ʲ` for every `k ≤ j`.

## Why the cap by `2⁻ʲ`

`exists_delta_norm_commutator_sqrt` produces, for each bound `M` and target `ε`,
*some* positive threshold.  It says nothing about how that threshold varies with
`ε`, so a schedule built from it directly need not tend to zero.  Capping the
chosen threshold by `ε` itself repairs this at no cost — a smaller threshold is
still a valid one — and it is what makes `stageTol` vanish, which is what the
asymptotic centrality of the finished unit needs.

## Why a recursion rather than a finite infimum

`stageTol` has to be antitone, and it has to dominate a minimum over the pairs
`k ≤ i ≤ j`.  Taking the minimum by recursion (`minDeltaUpTo` over `k`, then
`stageTol` over `j`) makes both facts one-line inductions, where a double
`Finset.inf'` would make them lattice bookkeeping.

## How it is spent

`norm_commutator_sqrt_piece_lt` is the only consumer.  At stage `j` the
recursion will know `‖[eⱼ, S_k]‖ < εⱼ` and `‖[e_{j+1}, S_k]‖ < ε_{j+1} ≤ εⱼ`, so
the piece — which is exactly `e_{j+1} - eⱼ` — has commutator below `2εⱼ`, and
that lemma converts it into `2⁻ʲ`.  Summability of `Σⱼ ‖[dⱼ, S_k]‖` is then
comparison on the tail `j ≥ k`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## A chosen modulus -/

/-- A choice of threshold for `exists_delta_norm_commutator_sqrt`, capped by the
target so that it shrinks with it. -/
def sqrtDelta (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M ε : ℝ) : ℝ :=
  if h : 0 < ε then min (exists_delta_norm_commutator_sqrt (H := H) M ε h).choose ε else 1

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sqrtDelta_pos (M : ℝ) {ε : ℝ} (hε : 0 < ε) : 0 < sqrtDelta H M ε := by
  rw [sqrtDelta, dif_pos hε]
  exact lt_min (exists_delta_norm_commutator_sqrt (H := H) M ε hε).choose_spec.1 hε

theorem sqrtDelta_le_self (M : ℝ) {ε : ℝ} (hε : 0 < ε) : sqrtDelta H M ε ≤ ε := by
  rw [sqrtDelta, dif_pos hε]
  exact min_le_right _ _

theorem norm_commutator_sqrt_lt {M ε : ℝ} (hε : 0 < ε) {a b : H →L[ℂ] H}
    (h0 : 0 ≤ a) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M)
    (h : ‖a * b - b * a‖ < sqrtDelta H M ε) :
    ‖CFC.sqrt a * b - b * CFC.sqrt a‖ < ε := by
  rw [sqrtDelta, dif_pos hε] at h
  exact (exists_delta_norm_commutator_sqrt (H := H) M ε hε).choose_spec.2 a b h0 ha hb
    (lt_of_lt_of_le h (min_le_left _ _))

/-! ## A positive contraction has norm at most one -/

/-- The bound the modulus asks of its first argument, for the pieces. -/
theorem norm_le_one_of_nonneg_of_le_one {a : H →L[ℂ] H} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    ‖a‖ ≤ 1 := by
  refine le_trans (CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 h1) ?_
  rcases subsingleton_or_nontrivial H with h | h
  · haveI := h
    have hz : (1 : H →L[ℂ] H) = 0 := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      rw [Subsingleton.elim x 0]
      simp
    rw [hz, norm_zero]
    norm_num
  · haveI := h
    exact le_of_eq norm_one

/-! ## The schedule -/

variable (S : ℕ → (H →L[ℂ] H))

/-- The least of the thresholds for the targets `S 0, …, S k` at level `j`. -/
def minDeltaUpTo (j : ℕ) : ℕ → ℝ
  | 0 => sqrtDelta H (max 1 ‖S 0‖) ((1 : ℝ) / 2 ^ j)
  | (k + 1) => min (minDeltaUpTo j k) (sqrtDelta H (max 1 ‖S (k + 1)‖) ((1 : ℝ) / 2 ^ j))

theorem minDeltaUpTo_pos (j k : ℕ) : 0 < minDeltaUpTo S j k := by
  induction k with
  | zero => exact sqrtDelta_pos _ (by positivity)
  | succ k ih => exact lt_min ih (sqrtDelta_pos _ (by positivity))

theorem minDeltaUpTo_le {j k k' : ℕ} (h : k' ≤ k) :
    minDeltaUpTo S j k ≤ sqrtDelta H (max 1 ‖S k'‖) ((1 : ℝ) / 2 ^ j) := by
  induction k with
  | zero =>
      rw [Nat.le_zero] at h
      subst h
      exact le_rfl
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
      · exact le_trans (min_le_left _ _) (ih (Nat.lt_succ_iff.mp h'))
      · subst h'
        exact min_le_right _ _

theorem minDeltaUpTo_le_pow (j k : ℕ) : minDeltaUpTo S j k ≤ (1 : ℝ) / 2 ^ j :=
  le_trans (minDeltaUpTo_le S (Nat.zero_le k)) (sqrtDelta_le_self _ (by positivity))

/-- **The schedule.**  Positive, antitone, at most `2⁻ʲ⁻¹`, and at most half the
least threshold at every earlier level. -/
def stageTol : ℕ → ℝ
  | 0 => minDeltaUpTo S 0 0 / 2
  | (j + 1) => min (stageTol j) (minDeltaUpTo S (j + 1) (j + 1) / 2)

theorem stageTol_pos (j : ℕ) : 0 < stageTol S j := by
  induction j with
  | zero => exact half_pos (minDeltaUpTo_pos S 0 0)
  | succ j ih => exact lt_min ih (half_pos (minDeltaUpTo_pos S (j + 1) (j + 1)))

theorem stageTol_antitone : Antitone (stageTol S) :=
  antitone_nat_of_succ_le fun _ ↦ min_le_left _ _

theorem stageTol_le_half (j : ℕ) : stageTol S j ≤ minDeltaUpTo S j j / 2 := by
  cases j with
  | zero => exact le_rfl
  | succ _ => exact min_le_right _ _

theorem stageTol_le_pow (j : ℕ) : stageTol S j ≤ (1 : ℝ) / 2 ^ j / 2 :=
  le_trans (stageTol_le_half S j) (by gcongr; exact minDeltaUpTo_le_pow S j j)

theorem tendsto_stageTol : Tendsto (stageTol S) atTop (𝓝 0) := by
  refine squeeze_zero (fun j ↦ (stageTol_pos S j).le) (stageTol_le_pow S) ?_
  have h : Tendsto (fun j : ℕ ↦ (1 : ℝ) / 2 ^ j) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1:ℝ) / 2 < 1)
  simpa using h.div_const 2

/-! ## How the schedule is spent -/

/-- **The only consumer.**  A piece whose commutator with `S k` is below twice
the stage tolerance has a square root commuting with `S k` to within `2⁻ʲ`. -/
theorem norm_commutator_sqrt_piece_lt {j k : ℕ} (hk : k ≤ j) {a : H →L[ℂ] H}
    (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (h : ‖a * S k - S k * a‖ < 2 * stageTol S j) :
    ‖CFC.sqrt a * S k - S k * CFC.sqrt a‖ < (1 : ℝ) / 2 ^ j := by
  refine norm_commutator_sqrt_lt (M := max 1 ‖S k‖) (by positivity)
    h0 (le_trans (norm_le_one_of_nonneg_of_le_one h0 h1) (le_max_left _ _))
    (le_max_right _ _) (lt_of_lt_of_le h ?_)
  calc 2 * stageTol S j ≤ 2 * (minDeltaUpTo S j j / 2) := by
        gcongr
        exact stageTol_le_half S j
    _ = minDeltaUpTo S j j := by ring
    _ ≤ sqrtDelta H (max 1 ‖S k‖) ((1 : ℝ) / 2 ^ j) := minDeltaUpTo_le S hk

end

end ShulmanFill
end GroupApproximation
