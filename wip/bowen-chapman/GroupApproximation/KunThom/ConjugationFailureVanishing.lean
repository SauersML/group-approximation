import GroupApproximation.KunThom.NormalizationFromCriterion
import GroupApproximation.KunThom.RelativeFunctorEstimate

/-!
# Vanishing conjugation failures of a compressor

Kun--Thom's relative functor (arXiv:2608.06222v3, Lemma 4.3) compares the
generators of `Γ` on the new blocks with the words `ws s` representing `t s t⁻¹`
on the old blocks, through the permutation `u = A(t)` of a compressor `t`.  The
step 9 budget (`BlockPatching.BlockEmbedding.sum_stepNineBudget_le`) carries
two totals of localized conjugation failures, for `u` and for `u⁻¹`.  This
module proves that both are negligible along any sofic approximation.

* `vanishing_hammingDistance_conj_wordAct`: if the word `w` evaluates to
  `t g t⁻¹`, then `d_H(A(t) A(g) A(t)⁻¹, A(w))` vanishes.  Here `A(w)` is the
  letter-by-letter product `FinitePartialBijection.wordAct`, which equals
  `SoficApproximation.evaluateWord` (`wordAct_map_eq_evaluateWord`), so the
  word step is `SoficApproximation.word_close`, and the conjugation step is
  `hamming_conj_vanishing`.
* `card_filter_conj_ne_le` and `hammingDistance_inv_conj`: the ambient counts
  `#{y | q (a y) ≠ b (q y)}` and their `q⁻¹` forms are Hamming disagreements of
  conjugates.
* `negligible_card_conj_ne` and `negligible_card_inv_conj_ne`: the per-label
  ambient failures are negligible.
* `negligible_sum_card_conjFailure` and `negligible_sum_card_conjFailure_inv`:
  for block data whose ambient label action is `A(ι l)`, the two totals of
  `RelativeFunctorEstimate.conjFailure` in the step 9 budget are negligible,
  through `RelativeFunctorEstimate.sum_card_conjFailure_le`.
-/

namespace GroupApproximation
namespace ConjugationFailureVanishing

open BlockPatching

universe u

/-- The word action of labels mapped into a group is the letter-by-letter
evaluation of the mapped word. -/
theorem wordAct_map_eq_evaluateWord {G : Type*} [Group G] {Y : FiniteModel} {L : Type*}
    (τ : G → Equiv.Perm Y) (ι : L → G) (w : List L) :
    FinitePartialBijection.wordAct (fun l ↦ τ (ι l)) w =
      SoficApproximation.evaluateWord τ (w.map ι) := by
  induction w with
  | nil => rfl
  | cons l w ih => exact congrArg (fun x ↦ τ (ι l) * x) ih

/-- **Ambient conjugation defect.**  If the word `w` in the labels evaluates to
`t g t⁻¹`, the conjugate `A(t) A(g) A(t)⁻¹` and the word action `A(w)` have
vanishing Hamming distance. -/
theorem vanishing_hammingDistance_conj_wordAct {G : Type} [Group G]
    (S : SoficApproximation G) {L : Type*} (ι : L → G) (t g : G) (w : List L)
    (hw : (w.map ι).prod = t * g * t⁻¹) :
    Vanishing fun n ↦ hammingDistance (S.model n)
      (S.map n t * S.map n g * (S.map n t)⁻¹)
      (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w) := by
  have hconj := S.hamming_conj_vanishing t g
  have hword : Vanishing fun n ↦ hammingDistance (S.model n) (S.map n (w.map ι).prod)
      (SoficApproximation.evaluateWord (S.map n) (w.map ι)) :=
    SequentialNormalization.vanishing_of_eventually_lt
      (fun _ ↦ hammingDistance_nonnegative _ _ _) (S.word_close (w.map ι))
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    (hconj.add hword)
  show hammingDistance (S.model n) (S.map n t * S.map n g * (S.map n t)⁻¹)
      (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w) ≤
    hammingDistance (S.model n) (S.map n (t * g * t⁻¹))
        (S.map n t * S.map n g * (S.map n t)⁻¹) +
      hammingDistance (S.model n) (S.map n (w.map ι).prod)
        (SoficApproximation.evaluateWord (S.map n) (w.map ι))
  have htri := hammingDistance_triangle (S.model n) (S.map n t * S.map n g * (S.map n t)⁻¹)
    (S.map n (t * g * t⁻¹)) (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w)
  have e₁ : hammingDistance (S.model n) (S.map n t * S.map n g * (S.map n t)⁻¹)
      (S.map n (t * g * t⁻¹)) =
      hammingDistance (S.model n) (S.map n (t * g * t⁻¹))
        (S.map n t * S.map n g * (S.map n t)⁻¹) :=
    hammingDistance_comm _ _ _
  have hprod : S.map n (t * g * t⁻¹) = S.map n (w.map ι).prod := by rw [hw]
  have e₂ : hammingDistance (S.model n) (S.map n (t * g * t⁻¹))
      (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w) =
      hammingDistance (S.model n) (S.map n (w.map ι).prod)
        (SoficApproximation.evaluateWord (S.map n) (w.map ι)) := by
    rw [hprod, wordAct_map_eq_evaluateWord (S.map n) ι w]
  linarith

/-- Conjugating by a permutation carries the failures `q (a y) ≠ b (q y)` onto
the disagreement of `q a q⁻¹` and `b`. -/
theorem card_filter_conj_ne_le {Y : FiniteModel} (q a b : Equiv.Perm Y) :
    (Finset.univ.filter fun y : Y ↦ q (a y) ≠ b (q y)).card ≤
      (hammingDisagreement (q * a * q⁻¹) b).card := by
  have himage : (Finset.univ.filter fun y : Y ↦ q (a y) ≠ b (q y)).image q ⊆
      hammingDisagreement (q * a * q⁻¹) b := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rw [mem_hammingDisagreement]
    have hy' : q (a y) ≠ b (q y) := (Finset.mem_filter.mp hy).2
    have e : (q * a * q⁻¹) (q y) = q (a y) := by
      show q (a (q.symm (q y))) = q (a y)
      rw [Equiv.symm_apply_apply]
    rw [e]
    exact hy'
  calc (Finset.univ.filter fun y : Y ↦ q (a y) ≠ b (q y)).card
      = ((Finset.univ.filter fun y : Y ↦ q (a y) ≠ b (q y)).image q).card :=
        (Finset.card_image_of_injective _ q.injective).symm
    _ ≤ (hammingDisagreement (q * a * q⁻¹) b).card := Finset.card_le_card himage

/-- The Hamming distance of `q⁻¹ b q` and `a` equals that of `q a q⁻¹` and `b`. -/
theorem hammingDistance_inv_conj (Y : FiniteModel) (q a b : Equiv.Perm Y) :
    hammingDistance Y (q⁻¹ * b * q) a = hammingDistance Y (q * a * q⁻¹) b := by
  have e₁ : hammingDistance Y (q * (q⁻¹ * b * q)) (q * a) =
      hammingDistance Y (q⁻¹ * b * q) a :=
    hammingDistance_left_invariant Y q _ _
  have e₂ : hammingDistance Y (q * (q⁻¹ * b * q) * q⁻¹) (q * a * q⁻¹) =
      hammingDistance Y (q * (q⁻¹ * b * q)) (q * a) :=
    hammingDistance_right_invariant Y _ _ q⁻¹
  have e₃ : q * (q⁻¹ * b * q) * q⁻¹ = b := by group
  rw [e₃] at e₂
  rw [← e₁, ← e₂]
  exact hammingDistance_comm Y b (q * a * q⁻¹)

/-- **Per-label ambient failures of `u`.**  The points `y` with
`A(t) (A(g) y) ≠ A(w) (A(t) y)` have negligible mass. -/
theorem negligible_card_conj_ne {G : Type} [Group G] (S : SoficApproximation G)
    {L : Type*} (ι : L → G) (t g : G) (w : List L) (hw : (w.map ι).prod = t * g * t⁻¹) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((Finset.univ.filter fun y : S.model n ↦ S.map n t (S.map n g y) ≠
        FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w (S.map n t y)).card : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_) (e := fun n ↦ ((hammingDisagreement (S.map n t * S.map n g * (S.map n t)⁻¹)
      (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w)).card : ℝ))
    (vanishing_hammingDistance_conj_wordAct S ι t g w hw)
  exact_mod_cast card_filter_conj_ne_le (S.map n t) (S.map n g)
    (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w)

/-- **Per-label ambient failures of `u⁻¹`.**  The points `y` with
`A(t)⁻¹ (A(w) y) ≠ A(g) (A(t)⁻¹ y)` have negligible mass. -/
theorem negligible_card_inv_conj_ne {G : Type} [Group G] (S : SoficApproximation G)
    {L : Type*} (ι : L → G) (t g : G) (w : List L) (hw : (w.map ι).prod = t * g * t⁻¹) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((Finset.univ.filter fun y : S.model n ↦
        (S.map n t)⁻¹ (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w y) ≠
          S.map n g ((S.map n t)⁻¹ y)).card : ℝ) := by
  have hv := vanishing_hammingDistance_conj_wordAct S ι t g w hw
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_) (e := fun n ↦ ((hammingDisagreement ((S.map n t)⁻¹ *
      FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w * (S.map n t)⁻¹⁻¹)
      (S.map n g)).card : ℝ)) ?_
  · exact_mod_cast card_filter_conj_ne_le (S.map n t)⁻¹
      (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w) (S.map n g)
  · refine Vanishing.congr hv fun n ↦ ?_
    show hammingDistance (S.model n) (S.map n t * S.map n g * (S.map n t)⁻¹)
        (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w) =
      hammingDistance (S.model n) ((S.map n t)⁻¹ *
        FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w * (S.map n t)⁻¹⁻¹)
        (S.map n g)
    rw [inv_inv, hammingDistance_inv_conj (S.model n) (S.map n t) (S.map n g)
      (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) w)]

/-- **Totals of `u`.**  For block data whose ambient label action is `A(ι l)`
and words `ws s` evaluating to `t (ι s) t⁻¹`, the total localized conjugation
failures of `A(t)` from the labels to the words are negligible. -/
theorem negligible_sum_card_conjFailure {G : Type} [Group G] (S : SoficApproximation G)
    {L : Type*} [Fintype L] (ι : L → G) (ws : L → List L) (t : G)
    (hws : ∀ s, ((ws s).map ι).prod = t * ι s * t⁻¹)
    {I : ℕ → Type u} [∀ n, Fintype (I n)] (E : ∀ n, BlockEmbedding (S.model n) (I n))
    (A : ∀ n, BlockAction (E n) L) (hA : ∀ n l, (A n).act l = S.map n (ι l)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (S.map n t) (A n)
        (RelativeFunctorEstimate.wordBlockAction (A n) ws) C s).card : ℕ) : ℝ) := by
  have hper : ∀ s ∈ (Finset.univ : Finset L),
      Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
        ((Finset.univ.filter fun y : S.model n ↦ S.map n t (S.map n (ι s) y) ≠
          FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) (S.map n t y)).card :
            ℝ) :=
    fun s _ ↦ negligible_card_conj_ne S ι t (ι s) (ws s) (hws s)
  have hsum := Negligible.sum Finset.univ _ hper
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_) hsum
  have hnat : ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (S.map n t) (A n)
      (RelativeFunctorEstimate.wordBlockAction (A n) ws) C s).card ≤
      ∑ s ∈ (Finset.univ : Finset L),
        (Finset.univ.filter fun y : S.model n ↦ S.map n t (S.map n (ι s) y) ≠
          FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) (S.map n t y)).card := by
    refine Finset.sum_le_sum fun s _ ↦ ?_
    have h := RelativeFunctorEstimate.sum_card_conjFailure_le (E n) (S.map n t) (A n)
      (RelativeFunctorEstimate.wordBlockAction (A n) ws) s
    refine h.trans (Finset.card_le_card fun y hy ↦ ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hw : (RelativeFunctorEstimate.wordBlockAction (A n) ws).act s =
        FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) := by
      show FinitePartialBijection.wordAct (A n).act (ws s) = _
      rw [show (A n).act = fun l ↦ S.map n (ι l) from funext (hA n)]
    rw [hA n s, hw] at hy
    exact hy
  show ((∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (S.map n t) (A n)
      (RelativeFunctorEstimate.wordBlockAction (A n) ws) C s).card : ℕ) : ℝ) ≤
    ∑ s ∈ (Finset.univ : Finset L),
      ((Finset.univ.filter fun y : S.model n ↦ S.map n t (S.map n (ι s) y) ≠
        FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) (S.map n t y)).card : ℝ)
  exact_mod_cast hnat

/-- **Totals of `u⁻¹`.**  The total localized conjugation failures of `A(t)⁻¹`
from the words back to the labels are negligible. -/
theorem negligible_sum_card_conjFailure_inv {G : Type} [Group G] (S : SoficApproximation G)
    {L : Type*} [Fintype L] (ι : L → G) (ws : L → List L) (t : G)
    (hws : ∀ s, ((ws s).map ι).prod = t * ι s * t⁻¹)
    {I : ℕ → Type u} [∀ n, Fintype (I n)] (E : ∀ n, BlockEmbedding (S.model n) (I n))
    (A : ∀ n, BlockAction (E n) L) (hA : ∀ n l, (A n).act l = S.map n (ι l)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (S.map n t)⁻¹
        (RelativeFunctorEstimate.wordBlockAction (A n) ws) (A n) C s).card : ℕ) : ℝ) := by
  have hper : ∀ s ∈ (Finset.univ : Finset L),
      Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
        ((Finset.univ.filter fun y : S.model n ↦
          (S.map n t)⁻¹ (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) y) ≠
            S.map n (ι s) ((S.map n t)⁻¹ y)).card : ℝ) :=
    fun s _ ↦ negligible_card_inv_conj_ne S ι t (ι s) (ws s) (hws s)
  have hsum := Negligible.sum Finset.univ _ hper
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_) hsum
  have hnat : ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (S.map n t)⁻¹
      (RelativeFunctorEstimate.wordBlockAction (A n) ws) (A n) C s).card ≤
      ∑ s ∈ (Finset.univ : Finset L),
        (Finset.univ.filter fun y : S.model n ↦
          (S.map n t)⁻¹ (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) y) ≠
            S.map n (ι s) ((S.map n t)⁻¹ y)).card := by
    refine Finset.sum_le_sum fun s _ ↦ ?_
    have h := RelativeFunctorEstimate.sum_card_conjFailure_le (E n) (S.map n t)⁻¹
      (RelativeFunctorEstimate.wordBlockAction (A n) ws) (A n) s
    refine h.trans (Finset.card_le_card fun y hy ↦ ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hw : (RelativeFunctorEstimate.wordBlockAction (A n) ws).act s =
        FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) := by
      show FinitePartialBijection.wordAct (A n).act (ws s) = _
      rw [show (A n).act = fun l ↦ S.map n (ι l) from funext (hA n)]
    rw [hA n s, hw] at hy
    exact hy
  show ((∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure (E n) (S.map n t)⁻¹
      (RelativeFunctorEstimate.wordBlockAction (A n) ws) (A n) C s).card : ℕ) : ℝ) ≤
    ∑ s ∈ (Finset.univ : Finset L),
      ((Finset.univ.filter fun y : S.model n ↦
        (S.map n t)⁻¹ (FinitePartialBijection.wordAct (fun l ↦ S.map n (ι l)) (ws s) y) ≠
          S.map n (ι s) ((S.map n t)⁻¹ y)).card : ℝ)
  exact_mod_cast hnat

end ConjugationFailureVanishing
end GroupApproximation
