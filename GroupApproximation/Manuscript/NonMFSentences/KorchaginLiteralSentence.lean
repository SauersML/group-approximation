import GroupApproximation.Manuscript.OneSidedMFRadical.IntroductionClaimSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# Korchagin's reformulation at the printed definition (tex 99–102)

`non_mf_groups_exist.tex`, Introduction (lines 87–102):

> A countable group `G` is MF if there are positive integers `d_n` and maps
> `V_n : G → U(d_n)`, with `V_n(1) = 1`, such that
> `‖V_n(gh) − V_n(g)V_n(h)‖ → 0` and `limsup_n ‖V_n(g) − 1‖ > 0` for `g ≠ 1`.
> For countable `G`, the second condition may equivalently be required along the full
> sequence with a constant independent of `g`~\cite[Propositions~2 and~7]{Korchagin}.

`KorchaginFullSequenceSentence` proves the reformulation between the corona form
`IsOperatorMF` and `WeakMFApproximation`.  This module states the sentence between the two
printed model conditions themselves.  Both sides keep the printed first condition and
`V_n(1) = 1`.  The left side has the printed `limsup` separation.  The right side has one
positive constant `δ`, independent of `g`, with `δ ≤ ‖V_n(g) − 1‖` at every index of the
sequence from some point on.

* Forward: the printed definition gives `IsCDEOperatorMF` (`manuscriptIntroductionMFDefinition`),
  hence a sequential approximation with one separation constant
  (`isCDEOperatorMF_iff_nonempty_weakMFApproximation`, whose forward half is Korchagin's
  assembly `exists_weakMFApproximation`).  Normalizing each coordinate by `V_n(1)⁻¹`
  (`normalizedMap`) fixes `V_n(1) = 1` exactly, keeps the multiplicative defect below
  `ε`, and leaves `‖V_n(g) − 1‖ = ‖A_n(g) − A_n(1)‖ ≥ δ`.
* Backward: an eventual lower bound `δ > 0` bounds the `limsup` below by `δ`.

No hypothesis stands for a cited result: Korchagin's Propositions 2 and 7 are proved in the
tree.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace KorchaginLiteralSentence

open OneSidedMFRadical
open scoped Matrix.Norms.L2Operator

/-- **Printed (tex 99–102).**  For a countable group, the printed MF model condition with
`limsup` separation is equivalent to the same condition with separation required along the
full sequence, eventually, by one constant `δ > 0` independent of `g`. -/
def PrintedKorchaginLiteral : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
      (∀ n, 0 < Fintype.card (X n)) ∧
        (∀ n, V n 1 = 1) ∧
        (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
            (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
        (∀ g : G, g ≠ 1 → 0 < Filter.limsup
          (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop)) ↔
    (∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
      (∀ n, 0 < Fintype.card (X n)) ∧
        (∀ n, V n 1 = 1) ∧
        (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
            (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ g : G, g ≠ 1 → ∃ N, ∀ n ≥ N,
          δ ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖)

/-- Closed proof of the printed reformulation. -/
theorem manuscriptSentence_korchaginLiteral : PrintedKorchaginLiteral := by
  intro G _ _
  constructor
  · intro hlit
    have hCDE : IsCDEOperatorMF G := (manuscriptIntroductionMFDefinition G).mpr hlit
    obtain ⟨A⟩ := (isCDEOperatorMF_iff_nonempty_weakMFApproximation G).mp hCDE
    refine ⟨A.model, fun n g ↦ ⟨normalizedMap A n g, normalizedMap_isUnitary A n g⟩,
      A.modelNonempty, fun n ↦ Subtype.ext (normalizedMap_one A n), ?_,
      A.separation, A.separation_pos, ?_⟩
    · intro g h ε hε
      obtain ⟨N1, hN1⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
      obtain ⟨N2, hN2⟩ := A.asymptoticallyMultiplicative 1 1 (ε / 2) (by linarith)
      refine ⟨max N1 N2, fun n hn ↦ ?_⟩
      have h1 := hN1 n (le_trans (le_max_left N1 N2) hn)
      have h2 := hN2 n (le_trans (le_max_right N1 N2) hn)
      simp only [one_mul] at h2
      calc ‖normalizedMap A n (g * h) - normalizedMap A n g * normalizedMap A n h‖
          ≤ ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
                (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                  (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ +
              ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) -
                (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) *
                  (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
            norm_normalizedMap_mul_sub_le A n g h
        _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
        _ = ε := by ring
    · intro g hg
      obtain ⟨N, hN⟩ := A.separatedEventually g 1 hg
      refine ⟨N, fun n hn ↦ ?_⟩
      show A.separation ≤ ‖normalizedMap A n g - 1‖
      rw [norm_normalizedMap_sub_one A n g]
      exact hN n hn
  · rintro ⟨X, V, hX, hone1, hmul, δ, hδ, hsep⟩
    refine ⟨X, V, hX, hone1, hmul, fun g hg ↦ ?_⟩
    obtain ⟨N, hN⟩ := hsep g hg
    have hev : ∀ᶠ n in Filter.atTop, δ ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖ := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      exact hN n hn
    have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) := by
      refine Filter.isBoundedUnder_of ⟨2, fun n ↦ ?_⟩
      letI : Nonempty (X n) := Fintype.card_pos_iff.mp (hX n)
      have hv : ‖(V n g : Matrix (X n) (X n) ℂ)‖ = 1 :=
        CStarRing.norm_of_mem_unitary (V n g).2
      have hone : ‖(1 : Matrix (X n) (X n) ℂ)‖ = 1 := CStarRing.norm_one
      have htri := norm_sub_le (V n g : Matrix (X n) (X n) ℂ) (1 : Matrix (X n) (X n) ℂ)
      rw [hv, hone] at htri
      linarith
    exact lt_of_lt_of_le hδ (Filter.le_limsup_of_frequently_le hev.frequently hbdd)

end KorchaginLiteralSentence
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.KorchaginLiteralSentence.manuscriptSentence_korchaginLiteral
