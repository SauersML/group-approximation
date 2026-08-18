import GroupApproximation.Algebra.WordMetric
import GroupApproximation.Sofic.InvolutionCollapseMetric

/-!
# Steps 3 and 4 of the involutive collapse, against the printed objects

This module reproves the generator-normalization bound of Step 3 and the
displacement almost-cocycle of Step 4 of the proof sketch of
`\ref{thm:collapse}` against the objects the manuscript printed at the time,
repairing three recorded mismatches (`docs/COLLAPSE_STEP_AUDIT.md`, COL.17,
COL.19, COL.20).

**Read "the manuscript actually prints" historically.**  Commit `3a45fa60`
replaced that six-step sketch with a corona argument, so the word metric, the
displacement almost-cocycle and the generator-mass bound below no longer
correspond to any printed step; the header of `Sofic/CollapseJointCorner.lean`
records the change in full.  The three repairs are still repairs of what the
audit graded, and nothing here is wrong; it is simply no longer badgeable.

* **COL.17.**  The printed bound is `d_n(1,\gamma) \le |\gamma|_S k_n`
  for the *word length* `|\cdot|_S`, a minimum over all representing
  words.  `col17_eventually_dV_le_wordNorm_mul_kNorm` proves exactly that,
  with `|\cdot|_S = WordMetric.wordNorm`, by the manuscript's inference:
  induction along a word, using eventual translation invariance
  (`InvolutionCollapseMetric.eventual_invariance`) and the triangle
  inequality for the rank displacement
  (`InvolutionCollapseMetric.dV_triangle`).  Since the word chosen is a
  *shortest* one, this is strictly stronger than the same induction along
  an arbitrary chosen word.

* **COL.19.**  `bVec` here is the printed
  `b_n(\gamma) = k_n^{-1/2}(V_n(\gamma) - V_n(1))`, with no guard.  At the
  stages where `k_n = 0` the scalar `(\sqrt{k_n})^{-1}` is `0` by the
  junk-value convention for `Real.sqrt` and inversion, which is the only
  reading available for `k_n^{-1/2}` there; at every stage with `k_n \ge 1`
  it is literally the displayed vector.

* **COL.20.**  `col20_eventually_norm_bVec_sq_le` proves
  `\|b_n(\gamma)\|_{\mathrm F}^2 \le 4|\gamma|_S` **at large stages only**,
  as printed, rather than at every stage: the guard that bought the
  every-stage statement is gone, and the threshold is exactly the one
  produced by COL.17.

The nonvanishing anchor `eq:generator-mass` (COL.21) is reproved for the
unguarded vector in `col21_sum_normSq_bVec_eq_four`; for the printed
object it needs no capping hypothesis at all, only `k_n \ge 1`, which is
what the manuscript said while it printed the display.

One thing the guard was silently buying must be recovered: the ultralimit
machinery consumes `Ultralimit.IsBoundedSeq`, a bound at *every* stage.
`exists_norm_bVec_bound` supplies it for the printed object from the
eventual bound, since only finitely many stages precede the COL.17
threshold and each contributes a single finite value
(`exists_bound_of_eventually_bounded`).
-/

namespace GroupApproximation
namespace CollapseWordMetric

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-! ## The generating set as a symmetric alphabet -/

/-- A finite symmetric generating set, in the form the Kazhdan pair of
Step 3 delivers it, is a symmetric generating alphabet in the sense of
`WordMetric.IsSymmetricGeneratingSet`. -/
theorem isSymmetricGeneratingSet_coe
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) :
    WordMetric.IsSymmetricGeneratingSet (S : Set Γ) := by
  refine ⟨?_, hgen⟩
  intro x hx
  exact Finset.mem_coe.mpr (hsymm x (Finset.mem_coe.mp hx))

/-! ## Step 3: the word bound, along a shortest word -/

/-- List form of the Step-3 bound: along any word in the generators the
displacement from the basepoint is eventually at most the length of the
word times the generator normalization.

This is the manuscript's inference verbatim — translation invariance
(`eventual_invariance`, Step 2) peels one letter, the triangle inequality
(`dV_triangle`, Step 2) splits the displacement, and the single-letter
displacement is bounded by `k_n` because `k_n` is the *sum* over the
generating set. -/
theorem eventually_dV_prod_le
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (l : List Γ) (hl : ∀ x ∈ l, x ∈ S) :
    ∃ N, ∀ n ≥ N,
      dV B V n l.prod 1 ≤ l.length * kNorm B V S n := by
  induction l with
  | nil =>
      refine ⟨0, fun n _ ↦ ?_⟩
      have hzero : dV B V n (List.prod []) 1 = 0 := by
        show (V n (1 : Γ) - V n 1).rank = 0
        rw [sub_self]
        exact Matrix.rank_zero
      rw [hzero]
      exact Nat.zero_le _
  | cons a l ih =>
      obtain ⟨N₁, hN₁⟩ := ih fun x hx ↦ hl x (List.mem_cons_of_mem a hx)
      obtain ⟨N₂, hN₂⟩ := eventual_invariance B iota k V hVinv hVcomm
        hVconv a l.prod 1
      refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
      have haS : a ∈ S := hl a List.mem_cons_self
      have hstep : dV B V n (a * l.prod) a = dV B V n l.prod 1 := by
        have h := hN₂ n ((le_max_right _ _).trans hn)
        rwa [mul_one] at h
      calc
        dV B V n (List.prod (a :: l)) 1 =
            dV B V n (a * l.prod) 1 := by rw [List.prod_cons]
        _ ≤ dV B V n (a * l.prod) a + dV B V n a 1 :=
          dV_triangle B V n _ a 1
        _ ≤ l.length * kNorm B V S n + kNorm B V S n := by
          rw [hstep]
          exact Nat.add_le_add (hN₁ n ((le_max_left _ _).trans hn))
            (dV_le_kNorm B V haS n)
        _ = (a :: l).length * kNorm B V S n := by
          rw [List.length_cons]
          ring

/-- **COL.17**, as printed: `d_n(\gamma,1) \le |\gamma|_S\,k_n` eventually,
for the genuine word length `|\cdot|_S` of the Kazhdan generating set —
the minimum over *all* words representing `\gamma`, not the length of a
chosen word.

The proof runs the manuscript's induction along a *shortest* word, which
exists by `WordMetric.exists_isWord_length_eq`. -/
theorem col17_eventually_dV_le_wordNorm_mul_kNorm
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    ∃ N, ∀ n ≥ N,
      dV B V n γ 1 ≤ WordMetric.wordNorm (S : Set Γ) γ * kNorm B V S n := by
  obtain ⟨l, hl, hlen⟩ :=
    WordMetric.exists_isWord_length_eq (isSymmetricGeneratingSet_coe S hgen hsymm) γ
  obtain ⟨N, hN⟩ := eventually_dV_prod_le B iota k V S hVinv hVcomm hVconv l
    (fun x hx ↦ Finset.mem_coe.mp (hl.letters x hx))
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rwa [hl.prod_eq, hlen] at h

/-- **COL.17** in the manuscript's own orientation `d_n(1,\gamma)`.  The
rank displacement is symmetric (`dV_symm`), so this is the same
statement. -/
theorem col17_eventually_dV_one_le_wordNorm_mul_kNorm
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    ∃ N, ∀ n ≥ N,
      dV B V n 1 γ ≤ WordMetric.wordNorm (S : Set Γ) γ * kNorm B V S n := by
  obtain ⟨N, hN⟩ := col17_eventually_dV_le_wordNorm_mul_kNorm B iota k V S
    hgen hsymm hVinv hVcomm hVconv γ
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dV_symm B V n 1 γ]
  exact hN n hn

/-! ## The mass identity -/

omit [Group Γ] in
/-- The Frobenius mass of a displacement is four times its rank
(COL.11, restated here so this module is independent of the guarded
development). -/
theorem matMass_V_sub
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (n : ℕ) (γ₁ γ₂ : Γ) :
    ScaledKazhdanTransport.matMass (V n γ₁ - V n γ₂) =
      4 * (dV B V n γ₁ γ₂ : ℝ) := by
  have h := matMass_sub_eq_four_mul_rank
    ⟨(hVinv n γ₁).1, (hVinv n γ₁).2⟩ ⟨(hVinv n γ₂).1, (hVinv n γ₂).2⟩
    (hVcomm n γ₁ γ₂)
  rw [h, rank_halfSqProjection ⟨(hVinv n γ₁).1, (hVinv n γ₁).2⟩
    ⟨(hVinv n γ₂).1, (hVinv n γ₂).2⟩ (hVcomm n γ₁ γ₂)]
  rfl

/-! ## Step 4: the printed displacement vector -/

/-- **COL.19**, the printed object: the flattened, `\sqrt{k_n}`-normalized
displacement
`b_n(\gamma) = k_n^{-1/2}\bigl(V_n(\gamma) - V_n(1)\bigr)`,
with no guard.  At stages with `k_n = 0` the normalizing scalar is `0`,
which is the only available reading of `k_n^{-1/2}` there; Step 3 shows
those stages are finitely many. -/
noncomputable def bVec (n : ℕ) (γ : Γ) :
    EuclideanSpace ℂ (B.model n × B.model n) :=
  ((Real.sqrt (kNorm B V S n))⁻¹ : ℝ) • flatE (V n γ - V n 1)

/-- The displacement vector vanishes at the basepoint. -/
theorem bVec_one (n : ℕ) : bVec B V S n 1 = 0 := by
  unfold bVec
  rw [sub_self, flatE_zero, smul_zero]

/-- Where the generator normalization vanishes so does the vector. -/
theorem bVec_of_kNorm_eq_zero {n : ℕ} (hk : kNorm B V S n = 0) (γ : Γ) :
    bVec B V S n γ = 0 := by
  unfold bVec
  rw [hk]
  simp

/-- At a stage with positive generator normalization the squared norm of
the displacement vector is the normalized Frobenius mass. -/
theorem norm_bVec_sq_of_pos {n : ℕ} (hk : 0 < kNorm B V S n) (γ : Γ) :
    ‖bVec B V S n γ‖ ^ 2 =
      ScaledKazhdanTransport.matMass (V n γ - V n 1) /
        (kNorm B V S n : ℝ) := by
  unfold bVec
  have hkpos : (0 : ℝ) < (kNorm B V S n : ℝ) := by exact_mod_cast hk
  have hsqrtpos : (0 : ℝ) < Real.sqrt (kNorm B V S n) :=
    Real.sqrt_pos.mpr hkpos
  rw [norm_smul, mul_pow, norm_flatE_sq]
  have hns : ‖((Real.sqrt (kNorm B V S n))⁻¹ : ℝ)‖ ^ 2 =
      ((kNorm B V S n : ℝ))⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrtpos), inv_pow,
      Real.sq_sqrt hkpos.le]
  rw [hns]
  ring

/-- **COL.20**, as printed: `\|b_n(\gamma)\|_{\mathrm F}^2 \le 4|\gamma|_S`
**at every large stage**, against the genuine word length.

The threshold is the one delivered by COL.17; before it, nothing is
claimed.  At the finitely many stages with `k_n = 0` inside the range the
vector is zero, so the bound is trivially true there as well — but it is
the eventual statement that is proved, matching the manuscript. -/
theorem col20_eventually_norm_bVec_sq_le
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    ∃ N, ∀ n ≥ N,
      ‖bVec B V S n γ‖ ^ 2 ≤
        4 * (WordMetric.wordNorm (S : Set Γ) γ : ℝ) := by
  obtain ⟨N, hN⟩ := col17_eventually_dV_le_wordNorm_mul_kNorm B iota k V S
    hgen hsymm hVinv hVcomm hVconv γ
  refine ⟨N, fun n hn ↦ ?_⟩
  rcases Nat.eq_zero_or_pos (kNorm B V S n) with hk | hk
  · rw [bVec_of_kNorm_eq_zero B V S hk γ, norm_zero]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0]
    positivity
  · have hkpos : (0 : ℝ) < (kNorm B V S n : ℝ) := by exact_mod_cast hk
    rw [norm_bVec_sq_of_pos B V S hk γ, matMass_V_sub B V hVinv hVcomm n γ 1,
      div_le_iff₀ hkpos]
    have hcast : (dV B V n γ 1 : ℝ) ≤
        (WordMetric.wordNorm (S : Set Γ) γ : ℝ) * (kNorm B V S n : ℝ) := by
      exact_mod_cast hN n hn
    nlinarith [hcast]

/-- **COL.20** in norm form: past the Step-3 threshold the displacement
vector has norm at most `\sqrt{4|\gamma|_S}`. -/
theorem eventually_norm_bVec_le
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    ∃ N, ∀ n ≥ N,
      ‖bVec B V S n γ‖ ≤
        Real.sqrt (4 * (WordMetric.wordNorm (S : Set Γ) γ : ℝ)) := by
  obtain ⟨N, hN⟩ := col20_eventually_norm_bVec_sq_le B iota k V S
    hgen hsymm hVinv hVcomm hVconv γ
  refine ⟨N, fun n hn ↦ ?_⟩
  have hsq := hN n hn
  have hnn := norm_nonneg (bVec B V S n γ)
  nlinarith [Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ 4 * (WordMetric.wordNorm (S : Set Γ) γ : ℝ)),
    Real.sqrt_nonneg (4 * (WordMetric.wordNorm (S : Set Γ) γ : ℝ))]

/-- An eventually bounded real sequence is bounded: only finitely many
stages precede the threshold, and each contributes one finite value. -/
theorem exists_bound_of_eventually_bounded {f : ℕ → ℝ} :
    ∀ (N : ℕ) (C : ℝ), (∀ n, N ≤ n → f n ≤ C) → ∃ C', ∀ n, f n ≤ C' := by
  intro N
  induction N with
  | zero =>
      intro C h
      exact ⟨C, fun n ↦ h n (Nat.zero_le n)⟩
  | succ m ih =>
      intro C h
      refine ih (max C (f m)) ?_
      intro n hn
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hnm : n = m := by omega
        rw [hnm]
        exact le_max_right _ _
      · exact le_trans (h n hge) (le_max_left _ _)

/-- The printed displacement vectors of a fixed mover form a **bounded
sequence**, which is what the ultralimit machinery consumes.

The guarded development obtained this at every stage by fiat, from the
cap; here it is a consequence of the eventual COL.20 bound together with
the fact that only finitely many stages precede the threshold.  The
statement is definitionally `Ultralimit.IsBoundedSeq (fun n ↦ bVec …)`,
so it can be used directly wherever that predicate is required. -/
theorem exists_norm_bVec_bound
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    ∃ C : ℝ, ∀ n, ‖bVec B V S n γ‖ ≤ C := by
  obtain ⟨N, hN⟩ := eventually_norm_bVec_le B iota k V S
    hgen hsymm hVinv hVcomm hVconv γ
  exact exists_bound_of_eventually_bounded (f := fun n ↦ ‖bVec B V S n γ‖) N
    (Real.sqrt (4 * (WordMetric.wordNorm (S : Set Γ) γ : ℝ))) hN

/-- **COL.21**, the nonvanishing anchor `eq:generator-mass`, for the
printed vector: whenever `k_n \ge 1` the generators carry total squared
mass exactly four.

For the unguarded object this needs no capping hypothesis — only
`0 < k_n`, exactly as the manuscript stated it before `3a45fa60` deleted the
display. -/
theorem col21_sum_normSq_bVec_eq_four
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    {n : ℕ} (hk : 0 < kNorm B V S n) :
    ∑ a ∈ S, ‖bVec B V S n a‖ ^ 2 = 4 := by
  have hkpos : (0 : ℝ) < (kNorm B V S n : ℝ) := by exact_mod_cast hk
  calc
    ∑ a ∈ S, ‖bVec B V S n a‖ ^ 2 =
        ∑ a ∈ S, 4 * ((dV B V n a 1 : ℝ) / (kNorm B V S n : ℝ)) := by
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [norm_bVec_sq_of_pos B V S hk a, matMass_V_sub B V hVinv hVcomm n a 1]
      ring
    _ = 4 * ((∑ a ∈ S, (dV B V n a 1 : ℝ)) / (kNorm B V S n : ℝ)) := by
      rw [Finset.sum_div, Finset.mul_sum]
    _ = 4 := by
      have hsum : (∑ a ∈ S, (dV B V n a 1 : ℝ)) = (kNorm B V S n : ℝ) := by
        rw [show kNorm B V S n = ∑ a ∈ S, dV B V n a 1 from rfl]
        push_cast
        rfl
      rw [hsum, div_self (ne_of_gt hkpos)]
      norm_num

end CollapseWordMetric
end GroupApproximation
