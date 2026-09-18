import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidualMF.StageEstimates
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidualMF.LocalModel
import GroupApproximation.Sofic.SymmetricDoubleCovering
import GroupApproximation.Sofic.SigmaGroupMF
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidual.ExactResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# Operator MF of the terminal amalgam

Source: `non_mf_group_notes.tex`, `thm:exact-mf-residual` (the analytic input
`IsOperatorMF (Σ *_B (B × C₂))`), and Shulman (arXiv:2603.13564), Theorem 10.

For a countable residually finite group `G` and any subgroup `Γ`, the
symmetric double `G *_Γ G` is operator-norm MF.  Stage `n` uses the letters
`exhaustSet f n` and a finite local model of the ball of radius `2n + 1`
(`exists_localModel`).  The first copy of `G` acts on `ℂ^Y ⊕ ℂ^Y` by
`pairHom`, the second by its conjugate under the stage rotation (`stageRot`).
On `Γ` the two families differ by at most `π / (n + 1)` (`opLength_stage_le`),
so they glue in the corona; a nontrivial word moves the basis vector of the
identity to a different basis vector from some stage on, so the gluing is
faithful (`isOperatorMF_symmetricDouble_of_gluing`).

The terminal amalgam is the free-lamp flip extension of `Σ *_B Σ`, and `Σ` is
residually finite (`sigmaGroup_residuallyFinite`), which gives
`terminalAmalgam_isOperatorMF`.  Composed with NN01's
`notesExactMFResidual_iff`, this closes `notesExactMFResidual`.  The proof is
operator-norm approximate: the rotation angles only converge, and no exact
finite model is used for the double.
-/

namespace GroupApproximation.Full.NN01b

open GroupApproximation Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

section Exhaustion

variable {G : Type} [Group G]

open Classical in
/-- The first `n` values of `f` together with their inverses. -/
def exhaustSet (f : ℕ → G) (n : ℕ) : Finset G :=
  (Finset.range n).image f ∪ (Finset.range n).image fun i => (f i)⁻¹

open Classical in
theorem inv_mem_exhaustSet (f : ℕ → G) {n : ℕ} {g : G} (hg : g ∈ exhaustSet f n) :
    g⁻¹ ∈ exhaustSet f n := by
  unfold exhaustSet at hg ⊢
  rcases Finset.mem_union.mp hg with h | h
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, (inv_inv (f i)).symm⟩)

open Classical in
theorem exists_forall_mem_exhaustSet (f : ℕ → G) (hf : Function.Surjective f) (g : G) :
    ∃ N, ∀ n, N ≤ n → g ∈ exhaustSet f n := by
  obtain ⟨i, rfl⟩ := hf g
  refine ⟨i + 1, fun n hn => ?_⟩
  unfold exhaustSet
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)

/-- A word has all its letters in the eventual letter sets. -/
theorem exists_forall_letters_mem (S : ℕ → Finset G) (hSex : ∀ g, ∃ N, ∀ n, N ≤ n → g ∈ S n)
    (l : List (Bool × G)) : ∃ N, ∀ n, N ≤ n → ∀ p, p ∈ l → p.2 ∈ S n := by
  induction l with
  | nil => exact ⟨0, fun _ _ _ hp => absurd hp List.not_mem_nil⟩
  | cons q l ih =>
    obtain ⟨N₁, h₁⟩ := hSex q.2
    obtain ⟨N₂, h₂⟩ := ih
    refine ⟨max N₁ N₂, fun n hn p hp => ?_⟩
    rcases List.mem_cons.mp hp with h | h
    · rw [h]
      exact h₁ n (le_of_max_le_left hn)
    · exact h₂ n (le_of_max_le_right hn) p h

end Exhaustion

section Words

variable {G : Type} [Group G]

theorem coe_wordEval_apply {X : ℕ → FiniteModel}
    (Φ : Bool → G →* (∀ n, Matrix.unitaryGroup (X n) ℂ)) (l : List (Bool × G)) (n : ℕ) :
    ((wordEval G (fun b g => Φ b g) l n : Matrix.unitaryGroup (X n) ℂ) :
        Matrix (X n) (X n) ℂ) =
      wordEval G (fun b g => ((Φ b g n : Matrix.unitaryGroup (X n) ℂ) :
        Matrix (X n) (X n) ℂ)) l := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [wordEval_cons, wordEval_cons, Pi.mul_apply, Submonoid.coe_mul, ih]

/-- A word whose matrix at stage `n` moves a basis vector to a different one is
at operator distance at least one from the identity at that stage. -/
theorem one_le_opLength_wordEval_of_colE {X : ℕ → FiniteModel}
    (Φ : Bool → G →* (∀ n, Matrix.unitaryGroup (X n) ℂ)) (l : List (Bool × G)) (n : ℕ)
    {j i : X n}
    (h : ColE (wordEval G (fun b g => ((Φ b g n : Matrix.unitaryGroup (X n) ℂ) :
      Matrix (X n) (X n) ℂ)) l) j i) (hij : i ≠ j) :
    1 ≤ opLength (X n) (wordEval G (fun b g => Φ b g) l n) := by
  refine one_le_opLength_of_colE _ ?_ hij
  rw [coe_wordEval_apply Φ l n]
  exact h

end Words

section Stages

variable {G : Type} [Group G] {Γ : Subgroup G}

/-- The two unitary families of the construction, all stages at once. -/
def stageFamily (S : ℕ → Finset G) (Y : ℕ → FiniteModel)
    (act : ∀ n, Bool → G →* Equiv.Perm (Y n)) (ι : ∀ n, SymmetricDouble G Γ → Y n) :
    Bool → G →* (∀ n, Matrix.unitaryGroup (blockSumModel (Y n) (Y n)) ℂ)
  | true => MonoidHom.pi fun n => pairHom (Y n) (act n true) (act n false)
  | false => MonoidHom.pi fun n =>
      rotConjHom (Y n) (stageRot (S n) n (ι n)) (pairHom (Y n) (act n true) (act n false))

/-- **Stages give operator MF** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`; Shulman, Theorem 10). -/
theorem isOperatorMF_symmetricDouble_of_stages (S : ℕ → Finset G)
    (hSinv : ∀ n g, g ∈ S n → g⁻¹ ∈ S n) (hSex : ∀ g, ∃ N, ∀ n, N ≤ n → g ∈ S n)
    (Y : ℕ → FiniteModel) (act : ∀ n, Bool → G →* Equiv.Perm (Y n))
    (ι : ∀ n, SymmetricDouble G Γ → Y n)
    (hinj : ∀ n, Set.InjOn (ι n)
      (dblBall G Γ (S n) (n + (n + 1)) : Set (SymmetricDouble G Γ)))
    (hact : ∀ n, StageCompatible (S n) n (act n) (ι n)) :
    IsOperatorMF (SymmetricDouble G Γ) := by
  refine isOperatorMF_symmetricDouble_of_gluing G Γ (fun n => blockSumModel (Y n) (Y n))
    (fun n => Fintype.card_pos_iff.mpr ⟨Sum.inl (ι n 1)⟩) (stageFamily S Y act ι) ?_ ?_
  · intro c ε hε
    obtain ⟨Nc, hNc⟩ := hSex (c : G)
    obtain ⟨Nε, hNε⟩ := exists_nat_gt (Real.pi / ε)
    refine Filter.Eventually.filter_mono Nat.cofinite_eq_atTop.le
      (Filter.eventually_atTop.mpr ⟨max Nc Nε, fun n hn => ?_⟩)
    have hcS : (c : G) ∈ S n := hNc n (le_of_max_le_left hn)
    have hb := opLength_stage_le (S n) n (act n) (ι n) (hact n) c.2 hcS (hSinv n _ hcS)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    have hNn : (Nε : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.le_succ_of_le (le_of_max_le_right hn))
    have h2 : Real.pi < ((n + 1 : ℕ) : ℝ) * ε := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hNε hNn)
    have h5 : Real.pi / ((n + 1 : ℕ) : ℝ) < ε := (div_lt_iff₀' hn1).mpr h2
    have h6 : 2 * (Real.pi / 2 / ((n + 1 : ℕ) : ℝ)) = Real.pi / ((n + 1 : ℕ) : ℝ) := by ring
    show opLength (blockSumModel (Y n) (Y n))
      ((pairHom (Y n) (act n true) (act n false) (c : G))⁻¹ *
        rotConjHom (Y n) (stageRot (S n) n (ι n)) (pairHom (Y n) (act n true) (act n false))
          (c : G)) < ε
    exact lt_of_le_of_lt (hb.trans_eq h6) h5
  · intro l hl
    by_contra hne
    obtain ⟨N, hN⟩ := exists_forall_letters_mem S hSex l
    refine not_mem_nullCofiniteOpSubgroup_of_eventually
      (wordEval G (fun b g => stageFamily S Y act ι b g) l) (max N l.length)
      (fun n hn => ?_) hl
    have hlet : ∀ p, p ∈ l → p.2 ∈ S n := hN n (le_of_max_le_left hn)
    have hlen : l.length ≤ n := le_of_max_le_right hn
    refine one_le_opLength_wordEval_of_colE (stageFamily S Y act ι) l n
      (colE_wordEval _ (fun l' : List (Bool × G) =>
        (Sum.inl (ι n (wordEval G (fun b g => inDouble G Γ b g) l')) :
          blockSumModel (Y n) (Y n)))
        l ?_) ?_
    · rintro ⟨b, g⟩ l' hsuf
      have hsub : ∀ p, p ∈ l' → p.2 ∈ S n :=
        fun p hp => hlet p (hsuf.subset (List.mem_cons_of_mem _ hp))
      have hg : g ∈ S n := hlet (b, g) (hsuf.subset List.mem_cons_self)
      have h1 := hsuf.length_le
      rw [List.length_cons] at h1
      have hx : wordEval G (fun b g => inDouble G Γ b g) l' ∈ dblBall G Γ (S n) n :=
        dblBall_mono (by omega) (wordEval_mem_dblBall l' hsub)
      have hgx : inDouble G Γ b g * wordEval G (fun b g => inDouble G Γ b g) l' ∈
          dblBall G Γ (S n) n :=
        dblBall_mono (by omega) (letter_mem_dblBall b hg (wordEval_mem_dblBall l' hsub))
      cases b with
      | false => exact colE_stage_false (S n) n (act n) (ι n) (hact n) g hx hgx
      | true => exact colE_stage_true (S n) n (act n) (ι n) (hact n) g hx hgx
    · intro heq
      apply hne
      have hB : wordEval G (fun b g => inDouble G Γ b g) l ∈ dblBall G Γ (S n) (n + (n + 1)) :=
        dblBall_mono (by omega) (wordEval_mem_dblBall l hlet)
      have h10 : (1 : SymmetricDouble G Γ) ∈ dblBall G Γ (S n) 0 := by
        rw [dblBall_zero]
        exact Finset.mem_singleton_self 1
      have h1B : (1 : SymmetricDouble G Γ) ∈ dblBall G Γ (S n) (n + (n + 1)) :=
        dblBall_mono (Nat.zero_le _) h10
      exact hinj n (Finset.mem_coe.mpr hB) (Finset.mem_coe.mpr h1B) (Sum.inl_injective heq)

end Stages

/-- **Symmetric doubles of countable residually finite groups are operator MF**
(`thm:exact-mf-residual`, `non_mf_group_notes.tex`; Shulman, Theorem 10, at the
level of groups and operator-norm approximations). -/
theorem isOperatorMF_symmetricDouble_of_residuallyFinite (G : Type) [Group G] [Countable G]
    [Group.ResiduallyFinite G] (Γ : Subgroup G) : IsOperatorMF (SymmetricDouble G Γ) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat G
  choose Y act ι hinj hact using fun n : ℕ =>
    exists_localModel G Γ (dblBall G Γ (exhaustSet f n) (n + (n + 1)))
  exact isOperatorMF_symmetricDouble_of_stages (exhaustSet f)
    (fun _ _ hg => inv_mem_exhaustSet f hg) (exists_forall_mem_exhaustSet f hf) Y act ι hinj hact

/-- **The terminal amalgam `Σ *_B (B × C₂)` is operator MF** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem terminalAmalgam_isOperatorMF :
    IsOperatorMF TerminalQuotientPresentation.TerminalAmalgam := by
  letI : Group.ResiduallyFinite TerminalQuotientPresentation.SigmaGroup :=
    TerminalQuotientPresentation.sigmaGroup_residuallyFinite
  exact (isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble
    TerminalQuotientPresentation.SigmaGroup TerminalQuotientPresentation.sigmaBase).mpr
      (isOperatorMF_symmetricDouble_of_residuallyFinite _ _)

/-- **The exact MF residual of the notes, closed** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem notesExactMFResidual : NN01.NotesExactMFResidual :=
  NN01.notesExactMFResidual_iff.mpr terminalAmalgam_isOperatorMF

end

#audit_closed_axioms GroupApproximation.Full.NN01b.terminalAmalgam_isOperatorMF
#audit_closed_axioms GroupApproximation.Full.NN01b.notesExactMFResidual

end GroupApproximation.Full.NN01b
