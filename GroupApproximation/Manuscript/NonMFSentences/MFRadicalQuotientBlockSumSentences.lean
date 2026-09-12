import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Meta.AxiomGuard

/-!
# `G / Rad_MF(G)` is MF: the printed block-sum family

`non_mf_groups_exist.tex`, Section 2 (tex lines 372-379 at 73c867c5b):

> For countable `G` the quotient `G/Rad_MF(G)` is again MF, and hence the
> largest MF quotient of `G`: enumerate its nontrivial elements and separate
> each by an MF model, and at stage `n` take the direct sum of the first `n`
> models, each carried far enough along its own sequence to have
> multiplicative defect below `1/n` on the first `n` elements while still
> separating its own element.  This family is asymptotically multiplicative
> and separates every nontrivial element.

The conclusion of the first sentence is
`IntroSentences.manuscriptSentence_mfRadicalQuotientIsMFAndLargest`, whose proof
runs through `Sofic/NormMFUniversalCorona.isOperatorMF_of_normMFResidual_eq_bot`.
That proof builds exactly the printed family but keeps it internal.  This module
exposes the construction and proves the second sentence about it:

* `normMFResidual (normMFQuotient G) = ⊥`: every nontrivial element of the
  quotient is separated by an MF model (a marked operator norm asymptotic
  representation);
* for a countable group with trivial residual, with the nontrivial elements
  enumerated (`mark`) and the group enumerated (`enumerate`), the stage-`k`
  family is the block sum of the first `k + 1` marked models, the `i`-th carried
  to a stage where its multiplicative defect on the first `k + 1` elements (and
  `1`) is at most `1/(k+1)`; every model separates its own element at every
  stage;
* the block sums are asymptotically multiplicative and separate every
  nontrivial element: `‖φ_k(g) − 1‖` stays above a positive constant for all
  large `k`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The printed stage-`k` family**: the direct sum of the first `k + 1` marked
models, the `i`-th carried to stage `stage i k` of its own sequence. -/
def blockSumStage {Q : Type} [Group Q] {mark : ℕ → Q}
    (A : ∀ i : ℕ, MarkedOpAlmostRepresentation Q (mark i)) (stage : ℕ → ℕ → ℕ)
    (k : ℕ) : List (UnitaryBlock Q) :=
  (List.range (k + 1)).map fun i ↦
    { model := (A i).model (stage i k)
      map := fun g ↦ (A i).map (stage i k) g }

/-- Uniformize an eventual bound over a finite set. -/
theorem eventually_forall_finset_bound_nm {I : Type*}
    (S : Finset I) (f : I → ℕ → ℝ)
    (h : ∀ s ∈ S, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, f s n ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ s ∈ S, f s n ≤ ε := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨0, by simp⟩
  · intro i s _ ih h
    obtain ⟨N₁, h₁⟩ := h i (Finset.mem_insert_self i s) ε hε
    obtain ⟨N₂, h₂⟩ := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
    refine ⟨max N₁ N₂, fun n hn j hj ↦ ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h₁ n ((le_max_left _ _).trans hn)
    · exact h₂ n ((le_max_right _ _).trans hn) j hj

/-- **The printed family, every clause.**  For a countable group `Q` all of whose
nontrivial elements are separated by MF models (`normMFResidual Q = ⊥`) and which
has a nontrivial element: an enumeration `mark` of the nontrivial elements, a
separating marked model `A i` for each, an enumeration of `Q`, and stages, such
that the `i`-th model at stage `stage i k` has multiplicative defect at most
`1/(k+1)` on `1` and the first `k + 1` elements, separates its own element at
every stage, and the block sums `blockSumStage A stage k` are asymptotically
multiplicative and separate every nontrivial element. -/
def PrintedBlockSumFamily : Prop :=
  ∀ (Q : Type) [Group Q] [Countable Q], normMFResidual Q = ⊥ → ∀ g₀ : Q, g₀ ≠ 1 →
    ∃ (mark : ℕ → Q) (_ : ∀ i, mark i ≠ 1) (_ : ∀ g : Q, g ≠ 1 → ∃ i, mark i = g)
      (A : ∀ i : ℕ, MarkedOpAlmostRepresentation Q (mark i))
      (enumerate : ℕ → Q) (_ : Function.Surjective enumerate)
      (stage : ℕ → ℕ → ℕ),
      (∀ (i k : ℕ) (g h : Q), (g = 1 ∨ ∃ j ≤ k, enumerate j = g) →
        (h = 1 ∨ ∃ j ≤ k, enumerate j = h) →
          ‖((A i).map (stage i k) (g * h) :
              Matrix ((A i).model (stage i k)) ((A i).model (stage i k)) ℂ) -
            ((A i).map (stage i k) g :
              Matrix ((A i).model (stage i k)) ((A i).model (stage i k)) ℂ) *
              (A i).map (stage i k) h‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ i n : ℕ, (A i).separation ≤
        ‖((A i).map n (mark i) : Matrix ((A i).model n) ((A i).model n) ℂ) -
          (A i).map n 1‖) ∧
      (∀ g h : Q, Tendsto (fun k ↦
        ‖blockListMap (blockSumStage A stage k) (g * h) -
          blockListMap (blockSumStage A stage k) g *
            blockListMap (blockSumStage A stage k) h‖) atTop (nhds 0)) ∧
      (∀ g : Q, g ≠ 1 → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop,
        ε ≤ ‖blockListMap (blockSumStage A stage k) g - 1‖)

theorem manuscriptSentence_blockSumFamily : PrintedBlockSumFamily := by
  classical
  intro Q _ _ hres g₀ hg₀
  haveI : Nonempty {g : Q // g ≠ 1} := ⟨⟨g₀, hg₀⟩⟩
  obtain ⟨markNe, hmarkNe⟩ := exists_surjective_nat {g : Q // g ≠ 1}
  have hdetect (i : ℕ) :
      ∃ (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
        (rho : Q →* UniversalWeakMF U X), rho (markNe i : Q) ≠ 1 := by
    have hnot : (markNe i : Q) ∉ normMFResidual Q := by
      rw [hres]
      simpa using (markNe i).property
    rw [mem_normMFResidual_iff] at hnot
    unfold NormMFInvisible at hnot
    push Not at hnot
    exact hnot
  choose I U Y detector hdetector using hdetect
  let A : ∀ i : ℕ, MarkedOpAlmostRepresentation Q (markNe i : Q) :=
    fun i ↦ Classical.choice
      (exists_markedOpAlmostRepresentation_of_ne_one
        (U i) (Y i) (detector i) (hdetector i))
  obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat Q
  let F : ℕ → Finset Q :=
    fun k ↦ insert 1 ((Finset.range (k + 1)).image enumerate)
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hFmem : ∀ g : Q, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨k, rfl⟩ := henumerate g
    exact ⟨k, fun n hn ↦ hFmono hn (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨k, Finset.self_mem_range_succ k, rfl⟩))⟩
  have hFof : ∀ (k : ℕ) (g : Q), (g = 1 ∨ ∃ j ≤ k, enumerate j = g) → g ∈ F k := by
    intro k g hg
    rcases hg with rfl | ⟨j, hj, rfl⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  let η : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hη (k : ℕ) : 0 < η k := by
    dsimp [η]
    positivity
  have hstageExists (i k : ℕ) : ∃ n : ℕ,
      ∀ p ∈ F k ×ˢ F k,
        ‖((A i).map n (p.1 * p.2) :
            Matrix ((A i).model n) ((A i).model n) ℂ) -
          ((A i).map n p.1 : Matrix ((A i).model n) ((A i).model n) ℂ) *
            (A i).map n p.2‖ ≤ η k := by
    obtain ⟨N, hN⟩ := eventually_forall_finset_bound_nm (F k ×ˢ F k)
      (fun p n ↦
        ‖((A i).map n (p.1 * p.2) :
            Matrix ((A i).model n) ((A i).model n) ℂ) -
          ((A i).map n p.1 : Matrix ((A i).model n) ((A i).model n) ℂ) *
            (A i).map n p.2‖)
      (fun p _ ↦ (A i).asymptoticallyMultiplicative p.1 p.2)
      (hη k)
    exact ⟨N, hN N le_rfl⟩
  let stage : ℕ → ℕ → ℕ :=
    fun i k ↦ Classical.choose (hstageExists i k)
  have hstage (i k : ℕ) :
      ∀ p ∈ F k ×ˢ F k,
        ‖((A i).map (stage i k) (p.1 * p.2) :
            Matrix ((A i).model (stage i k)) ((A i).model (stage i k)) ℂ) -
          ((A i).map (stage i k) p.1 :
            Matrix ((A i).model (stage i k)) ((A i).model (stage i k)) ℂ) *
            (A i).map (stage i k) p.2‖ ≤ η k :=
    Classical.choose_spec (hstageExists i k)
  have hBmem {i k : ℕ} (hik : i ≤ k) :
      ({ model := (A i).model (stage i k)
         map := fun g ↦ (A i).map (stage i k) g } : UnitaryBlock Q)
        ∈ blockSumStage A stage k := by
    apply List.mem_map.mpr
    exact ⟨i, by simp; omega, rfl⟩
  have hblockDefect (k : ℕ) {C : UnitaryBlock Q}
      (hC : C ∈ blockSumStage A stage k) {g h : Q} (hg : g ∈ F k) (hh : h ∈ F k) :
      ‖(C.map (g * h) : Matrix C.model C.model ℂ) -
        (C.map g : Matrix C.model C.model ℂ) * C.map h‖ ≤ η k := by
    rcases List.mem_map.mp hC with ⟨i, _, rfl⟩
    exact hstage i k (g, h) (Finset.mem_product.mpr ⟨hg, hh⟩)
  have hmul : ∀ g h : Q, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ k ≥ N,
      ‖blockListMap (blockSumStage A stage k) (g * h) -
        blockListMap (blockSumStage A stage k) g *
          blockListMap (blockSumStage A stage k) h‖ ≤ ε := by
    intro g h ε hε
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h
    obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / ε)
    refine ⟨max (max Ng Nh) Ne, fun k hk ↦ ?_⟩
    have hg : g ∈ F k := hNg k ((le_max_left _ _).trans
      ((le_max_left _ _).trans hk))
    have hh : h ∈ F k := hNh k ((le_max_right _ _).trans
      ((le_max_left _ _).trans hk))
    have hsmall : η k ≤ ε := by
      dsimp [η]
      have hNek : (Ne : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (le_max_right (max Ng Nh) Ne).trans hk
      have hlt : (1 : ℝ) / ε < (k : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hlt
      linarith
    exact (norm_blockListMap_mul_sub_le Q (blockSumStage A stage k) g h (hη k).le
      (fun C hC ↦ hblockDefect k hC hg hh)).trans hsmall
  refine ⟨fun i ↦ (markNe i : Q), fun i ↦ (markNe i).property, fun g hg ↦ ?_,
    A, enumerate, henumerate, stage, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hmarkNe ⟨g, hg⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · intro i k g h hg hh
    exact hstage i k (g, h) (Finset.mem_product.mpr ⟨hFof k g hg, hFof k h hh⟩)
  · intro i n
    exact (A i).marked_separated n
  · intro g h
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hmul g h (ε / 2) (by linarith)
    refine ⟨N, fun k hk ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact (hN k hk).trans_lt (by linarith)
  · intro g hg
    obtain ⟨i, hi⟩ := hmarkNe ⟨g, hg⟩
    have himark : (markNe i : Q) = g := congrArg Subtype.val hi
    have hsep := (A i).separation_pos
    refine ⟨(A i).separation / 2, by linarith, ?_⟩
    obtain ⟨N, hN⟩ := hmul 1 1 ((A i).separation / 2) (by linarith)
    rw [eventually_atTop]
    refine ⟨max i N, fun k hk ↦ ?_⟩
    have hfar : (A i).separation ≤
        ‖blockListMap (blockSumStage A stage k) g -
          blockListMap (blockSumStage A stage k) 1‖ := by
      have hblock : (A i).separation ≤
          ‖((A i).map (stage i k) g :
              Matrix ((A i).model (stage i k)) ((A i).model (stage i k)) ℂ) -
            (A i).map (stage i k) 1‖ := by
        simpa only [himark] using (A i).marked_separated (stage i k)
      exact hblock.trans
        (norm_blockListMap_sub_ge_of_mem (hBmem (le_of_max_le_left hk)) g 1)
    have hone : ‖(1 : Matrix (blockListModel (blockSumStage A stage k))
          (blockListModel (blockSumStage A stage k)) ℂ) -
        blockListMap (blockSumStage A stage k) 1‖ ≤ (A i).separation / 2 := by
      have hdef := hN k (le_of_max_le_right hk)
      rw [mul_one] at hdef
      set W := blockListMap (blockSumStage A stage k) 1 with hW
      have hWmem : W ∈ Matrix.unitaryGroup (blockListModel (blockSumStage A stage k)) ℂ :=
        blockListMap_mem_unitaryGroup (blockSumStage A stage k) 1
      have hunit : star W * W = 1 := Unitary.star_mul_self_of_mem hWmem
      have hkey : (1 : Matrix (blockListModel (blockSumStage A stage k))
          (blockListModel (blockSumStage A stage k)) ℂ) - W = star W * (W - W * W) := by
        rw [mul_sub, ← mul_assoc, hunit, one_mul]
      haveI : Nonempty (blockListModel (blockSumStage A stage k)) :=
        Fintype.card_pos_iff.mp (card_blockListModel_pos_of_mem
          (hBmem (le_of_max_le_left hk)) ((A i).modelNonempty (stage i k)))
      have hstarnorm : ‖star W‖ = 1 := by
        rw [norm_star]
        exact CStarRing.norm_of_mem_unitary hWmem
      rw [hkey]
      calc ‖star W * (W - W * W)‖ ≤ ‖star W‖ * ‖W - W * W‖ := norm_mul_le _ _
        _ = ‖W - W * W‖ := by rw [hstarnorm, one_mul]
        _ ≤ (A i).separation / 2 := hdef
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (blockListMap (blockSumStage A stage k) g)
      (1 : Matrix (blockListModel (blockSumStage A stage k))
        (blockListModel (blockSumStage A stage k)) ℂ)
      (blockListMap (blockSumStage A stage k) 1)
    linarith

/-- **The printed quotient has trivial residual**: every nontrivial element of
`G / Rad_MF(G)` (`normMFQuotient G`) is separated by an MF model, so
`manuscriptSentence_blockSumFamily` applies to it. -/
def PrintedMFRadicalQuotientResidualTrivial : Prop :=
  ∀ (G : Type) [Group G] [Countable G], normMFResidual (normMFQuotient G) = ⊥

theorem manuscriptSentence_mfRadicalQuotientResidualTrivial :
    PrintedMFRadicalQuotientResidualTrivial := by
  intro G _ _
  haveI : Countable (normMFQuotient G) :=
    Function.Surjective.countable (QuotientGroup.mk'_surjective (normMFResidual G))
  exact normMFResidual_eq_bot_of_isOperatorMF normMFQuotient_isOperatorMF

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_blockSumFamily
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_mfRadicalQuotientResidualTrivial
