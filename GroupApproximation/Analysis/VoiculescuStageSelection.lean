import GroupApproximation.Analysis.VoiculescuAlmostOrthogonal
import GroupApproximation.Analysis.VoiculescuDefect

/-!
# (V1b) One stage: an average of the unit that almost commutes with finitely many operators

This is the step Arveson's convexity trick performs, done by hand.  Fix
finitely many targets `S 0, …, S (K-1)`, a tolerance `ε` and an index `m` past
which the average must live.  The average is

    `f = N⁻¹ ∑_{i < N} e_{sel i}` ,

a convex combination of members of the sequential unit, so it is compact,
self-adjoint, a contraction, and absorbs whatever all of `e_{sel i}` absorb.
What has to be arranged is the commutator bound, and that is where the indices
are chosen: `Analysis/VoiculescuDefect` says the products `D_q D_n⋆` of
defects tend to `0` as `n → ∞` for each fixed `q`, so a greedy recursion

    `sel 0 = m`,  `sel (j+1) = max (sel j + 1) (ψ (sel j))`

with `ψ q` a threshold past which all the targets' cross terms at `q` are below
`δ` gives `‖D_{sel i} D_{sel j}⋆‖ ≤ δ` for every `i < j` — and for `i > j` by
taking adjoints.  Then `Analysis/VoiculescuAlmostOrthogonal` bounds the sum by
`√(N M² + N² δ)`, and dividing by `N` leaves `√(M²/N + δ)`, which is below `ε`
once `N ≥ 2M²/ε²` and `δ = ε²/2`.

The recursion is written with a *single* previous value rather than the set of
all previous ones, which is what keeps it a structural `Nat` recursion: the
threshold at `sel i` is already passed by `sel (i+1)`, and `sel` is increasing,
so it is passed by every later `sel j` as well.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology Finset

noncomputable section

/-! ## The greedy selection -/

/-- **The greedy selection.**  Each index is past the previous one and past the
threshold `ψ` that the previous index demands. -/
def greedySelect (ψ : ℕ → ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => max (greedySelect ψ m j + 1) (ψ (greedySelect ψ m j))

theorem greedySelect_zero (ψ : ℕ → ℕ) (m : ℕ) : greedySelect ψ m 0 = m := rfl

theorem greedySelect_succ (ψ : ℕ → ℕ) (m j : ℕ) :
    greedySelect ψ m (j + 1) = max (greedySelect ψ m j + 1) (ψ (greedySelect ψ m j)) :=
  rfl

theorem lt_greedySelect_succ (ψ : ℕ → ℕ) (m j : ℕ) :
    greedySelect ψ m j < greedySelect ψ m (j + 1) := by
  rw [greedySelect_succ]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

theorem greedySelect_strictMono (ψ : ℕ → ℕ) (m : ℕ) : StrictMono (greedySelect ψ m) :=
  strictMono_nat_of_lt_succ (lt_greedySelect_succ ψ m)

theorem le_greedySelect (ψ : ℕ → ℕ) (m j : ℕ) : m ≤ greedySelect ψ m j := by
  induction j with
  | zero => exact le_of_eq (greedySelect_zero ψ m).symm
  | succ j ih => exact ih.trans (lt_greedySelect_succ ψ m j).le

/-- **The point of the recursion.**  A later index passes the threshold of an
earlier one, so the pairwise conditions hold for every pair. -/
theorem threshold_le_greedySelect (ψ : ℕ → ℕ) (m : ℕ) {i j : ℕ} (hij : i < j) :
    ψ (greedySelect ψ m i) ≤ greedySelect ψ m j := by
  have h1 : ψ (greedySelect ψ m i) ≤ greedySelect ψ m (i + 1) := by
    rw [greedySelect_succ]
    exact le_max_right _ _
  exact h1.trans ((greedySelect_strictMono ψ m).monotone hij)

/-! ## The stage -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- A finite sum of compact operators is compact. -/
theorem isCompactOperator_sum {ι : Type*} (s : Finset ι) (F : ι → (H →L[ℂ] H))
    (h : ∀ i ∈ s, IsCompactOperator (F i)) :
    IsCompactOperator (∑ i ∈ s, F i : H →L[ℂ] H) :=
  Finset.sum_induction F (fun T ↦ IsCompactOperator T) (fun _ _ ha hb ↦ ha.add hb)
    isCompactOperator_zero h

/-- **One stage of the quasicentral construction.**  Given finitely many
targets, a tolerance and a starting index, an average of late members of the
sequential unit commutes with all the targets to within the tolerance, and
absorbs every operator that all late members absorb.

The last clause is the absorption in the form the diagonal argument uses it:
whatever bound the tail of the unit achieves against `T`, the average achieves
too, because it is a convex combination of tail members. -/
theorem exists_stage_of_sequentialCompactUnit (u : SequentialCompactUnit H)
    (S : ℕ → (H →L[ℂ] H)) (K m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : H →L[ℂ] H, IsCompactOperator f ∧ IsSelfAdjoint f ∧ ‖f‖ ≤ 1 ∧
      (∀ k < K, ‖f * S k - S k * f‖ ≤ ε) ∧
      (∀ (T : H →L[ℂ] H) (d : ℝ),
        (∀ n, m ≤ n → ‖T - u.toFun n * T‖ ≤ d) → ‖T - f * T‖ ≤ d) := by
  classical
  -- a single bound for all the targets
  obtain ⟨M, hSbound⟩ : ∃ M : ℝ, ∀ k < K, 2 * ‖S k‖ ≤ M := by
    refine ⟨2 * (((Finset.range K).sup fun k ↦ ⌈‖S k‖⌉₊ : ℕ) : ℝ), ?_⟩
    intro k hk
    have h1 : ‖S k‖ ≤ ((⌈‖S k‖⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : (⌈‖S k‖⌉₊ : ℕ) ≤ ((Finset.range K).sup fun k ↦ ⌈‖S k‖⌉₊) :=
      Finset.le_sup (f := fun k ↦ ⌈‖S k‖⌉₊) (Finset.mem_range.mpr hk)
    have h3 : ((⌈‖S k‖⌉₊ : ℕ) : ℝ)
        ≤ ((((Finset.range K).sup fun k ↦ ⌈‖S k‖⌉₊ : ℕ)) : ℝ) := Nat.cast_le.mpr h2
    linarith
  -- how many members to average
  obtain ⟨N, hN0, hNbig⟩ : ∃ N : ℕ, 0 < N ∧ 2 * M ^ 2 / ε ^ 2 ≤ (N : ℝ) := by
    refine ⟨⌈2 * M ^ 2 / ε ^ 2⌉₊ + 1, Nat.succ_pos _, ?_⟩
    have h := Nat.le_ceil (2 * M ^ 2 / ε ^ 2)
    push_cast
    linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hNR
  have hNCne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN0.ne'
  have hnormc : ‖((N : ℂ))⁻¹‖ = ((N : ℝ))⁻¹ := by simp
  -- how small the cross terms must be
  obtain ⟨δ, hδpos, hsize⟩ : ∃ δ : ℝ, 0 < δ ∧
      (N : ℝ) * M ^ 2 + (N : ℝ) ^ 2 * δ ≤ ((N : ℝ) * ε) ^ 2 := by
    have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    refine ⟨ε ^ 2 / 2, div_pos hε2 (by norm_num), ?_⟩
    rw [div_le_iff₀ hε2] at hNbig
    nlinarith [mul_le_mul_of_nonneg_left hNbig hNR.le]
  -- the thresholds, and the selection
  have hcross : ∀ q : ℕ, ∃ p : ℕ, ∀ n, p ≤ n → ∀ k < K,
      ‖quasicentralDefect u (S k) q * star (quasicentralDefect u (S k) n)‖ ≤ δ := by
    intro q
    have hev : ∀ᶠ n in atTop, ∀ k ∈ Finset.range K,
        ‖quasicentralDefect u (S k) q * star (quasicentralDefect u (S k) n)‖ ≤ δ := by
      rw [eventually_all_finset]
      intro k _
      exact (tendsto_norm_quasicentralDefect_mul_star u (S k) q).eventually_le_const hδpos
    obtain ⟨p, hp⟩ := eventually_atTop.mp hev
    exact ⟨p, fun n hn k hk ↦ hp n hn k (Finset.mem_range.mpr hk)⟩
  choose ψ hψ using hcross
  have hoffdiag : ∀ k < K, ∀ i j : ℕ, i ≠ j →
      ‖quasicentralDefect u (S k) (greedySelect ψ m i)
        * star (quasicentralDefect u (S k) (greedySelect ψ m j))‖ ≤ δ := by
    intro k hk i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hψ (greedySelect ψ m i) (greedySelect ψ m j)
        (threshold_le_greedySelect ψ m h) k hk
    · have h2 := hψ (greedySelect ψ m j) (greedySelect ψ m i)
        (threshold_le_greedySelect ψ m h) k hk
      rw [← norm_star, star_mul, star_star]
      exact h2
  -- the average, clause by clause
  have hcompact : IsCompactOperator
      ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i) : H →L[ℂ] H) := by
    have h := IsCompactOperator.smul
      (isCompactOperator_sum (Finset.range N) (fun i ↦ u.toFun (greedySelect ψ m i))
        (fun i _ ↦ u.isCompact (greedySelect ψ m i))) ((N : ℂ)⁻¹)
    exact h
  have hsa : IsSelfAdjoint
      ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)) := by
    have hstarc : star ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by rw [star_inv₀, star_natCast]
    show star ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i))
      = (N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)
    rw [star_smul, hstarc, star_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ (u.isSelfAdjoint (greedySelect ψ m i)).star_eq
  have hnorm : ‖((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i))‖ ≤ 1 := by
    have h1 : ‖∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)‖ ≤ (N : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ Finset.range N, ‖u.toFun (greedySelect ψ m i)‖
          ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ u.norm_le (greedySelect ψ m i)
        _ = (N : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [norm_smul, hnormc]
    calc ((N : ℝ))⁻¹ * ‖∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)‖
        ≤ ((N : ℝ))⁻¹ * (N : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ hNne
  have hcomm : ∀ k < K,
      ‖((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)) * S k
        - S k * ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i))‖ ≤ ε := by
    intro k hk
    have hexp : ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)) * S k
        - S k * ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i))
        = (N : ℂ)⁻¹ • ∑ i ∈ Finset.range N,
            quasicentralDefect u (S k) (greedySelect ψ m i) := by
      simp only [quasicentralDefect_eq]
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
    have hAO : ‖∑ i ∈ Finset.range N, quasicentralDefect u (S k) (greedySelect ψ m i)‖
        ≤ (N : ℝ) * ε := by
      refine norm_sum_le_of_almostOrthogonal _ N M δ ε hδpos.le hε.le ?_ ?_ hsize
      · intro i _
        exact (norm_quasicentralDefect_le u (S k) _).trans (hSbound k hk)
      · intro i _ j _ hij
        exact hoffdiag k hk i j hij
    rw [hexp, norm_smul, hnormc]
    calc ((N : ℝ))⁻¹
          * ‖∑ i ∈ Finset.range N, quasicentralDefect u (S k) (greedySelect ψ m i)‖
        ≤ ((N : ℝ))⁻¹ * ((N : ℝ) * ε) := mul_le_mul_of_nonneg_left hAO (by positivity)
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  have habs : ∀ (T : H →L[ℂ] H) (d : ℝ), (∀ n, m ≤ n → ‖T - u.toFun n * T‖ ≤ d) →
      ‖T - ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)) * T‖ ≤ d := by
    intro T d hT
    have hexp : (N : ℂ)⁻¹ • ∑ i ∈ Finset.range N,
          (T - u.toFun (greedySelect ψ m i) * T)
        = T - ((N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i)) * T := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_mul,
        smul_sub, ← smul_mul_assoc, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul,
        inv_mul_cancel₀ hNCne, one_smul]
    have hsum : ‖∑ i ∈ Finset.range N, (T - u.toFun (greedySelect ψ m i) * T)‖
        ≤ (N : ℝ) * d := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ Finset.range N, ‖T - u.toFun (greedySelect ψ m i) * T‖
          ≤ ∑ _i ∈ Finset.range N, d :=
            Finset.sum_le_sum fun i _ ↦ hT (greedySelect ψ m i) (le_greedySelect ψ m i)
        _ = (N : ℝ) * d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← hexp, norm_smul, hnormc]
    calc ((N : ℝ))⁻¹ * ‖∑ i ∈ Finset.range N, (T - u.toFun (greedySelect ψ m i) * T)‖
        ≤ ((N : ℝ))⁻¹ * ((N : ℝ) * d) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = d := by rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  exact ⟨(N : ℂ)⁻¹ • ∑ i ∈ Finset.range N, u.toFun (greedySelect ψ m i),
    hcompact, hsa, hnorm, hcomm, habs⟩

end

end ShulmanFill
end GroupApproximation
