import GroupApproximation.GGT.HullSCUnconeExpansion
import GroupApproximation.GGT.OsinTheorem54SepSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 5: the points of a guessed path

A guessed path (`GGT/HullSCUnconeExpansion.lean`) is the expansion of a geodesic word of `J`, letter
by letter.  This module reads its points off the letters:

* `guessPath_at_letter` — after the expansions of the first `k` letters the path is at the `k`-th
  vertex of the geodesic word;
* `guessPath_in_letter` — inside the expansion of the `k`-th letter it is at that vertex times a
  prefix of the letter's expansion;
* `exists_letter_block` — every index of the path is at a letter boundary or strictly inside one
  letter's expansion;
* `prod_take_expLetters_inr` — a prefix of the expansion of a cyclic letter `gᵢᵗ` spells `gᵢ^{±s}`.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u v w

namespace Uncone

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

theorem expWord_take_append (g : I → Q) (w : List (RelLetter Q (Sum Lambda I))) (k : ℕ) :
    expWord g w = expWord g (w.take k) ++ expWord g (w.drop k) := by
  rw [← expWord_append, List.take_append_drop]

theorem expWord_drop_eq_cons (g : I → Q) (w : List (RelLetter Q (Sum Lambda I))) {k : ℕ}
    (hk : k < w.length) :
    expWord g (w.drop k) = expLetters g (w[k]'hk) ++ expWord g (w.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk, expWord_cons]

/-- **At a letter boundary the guessed path is at a vertex of the geodesic word.** -/
theorem guessPath_at_letter (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y : Q) (k : ℕ) :
    guessPath J g x y (expWord g ((geodWord J x y).take k)).length
      = vertex x (geodWord J x y) k := by
  have hlet : ∀ a ∈ (geodWord J x y).take k, J.IsLetter a :=
    fun a ha => (geodWord_spec J x y).1 a (List.take_subset k _ ha)
  unfold guessPath guessWord
  rw [expWord_take_append g (geodWord J x y) k, List.take_left' rfl,
    prod_expWord J g hg _ hlet, vertex_eq_mul_listVal_take]

/-- **Inside the expansion of a letter the guessed path is at that letter's vertex times a prefix
of its expansion.** -/
theorem guessPath_in_letter (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y : Q) {k : ℕ}
    (hk : k < (geodWord J x y).length) {s : ℕ}
    (hs : s ≤ (expLetters g ((geodWord J x y)[k]'hk)).length) :
    guessPath J g x y ((expWord g ((geodWord J x y).take k)).length + s)
      = vertex x (geodWord J x y) k * ((expLetters g ((geodWord J x y)[k]'hk)).take s).prod := by
  have hlet : ∀ a ∈ (geodWord J x y).take k, J.IsLetter a :=
    fun a ha => (geodWord_spec J x y).1 a (List.take_subset k _ ha)
  unfold guessPath guessWord
  rw [expWord_take_append g (geodWord J x y) k, expWord_drop_eq_cons g (geodWord J x y) hk,
    List.take_append_eq_append_take, List.take_of_length_le (by omega),
    List.take_append_eq_append_take, List.take_of_length_le (l := expLetters g _) (by omega),
    Nat.add_sub_cancel_left]
  have hzero : s - (expLetters g ((geodWord J x y)[k]'hk)).length = 0 := by omega
  rw [List.take_of_length_le (l := expLetters g _) hs, hzero, List.take_zero, List.append_nil,
    List.prod_append, prod_expWord J g hg _ hlet, vertex_eq_mul_listVal_take, mul_assoc]

/-- **Every index of the expansion is at a letter boundary or strictly inside one letter.** -/
theorem exists_letter_block (g : I → Q) :
    ∀ (w : List (RelLetter Q (Sum Lambda I))) (j : ℕ), j ≤ (expWord g w).length →
      (∃ k : ℕ, k ≤ w.length ∧ j = (expWord g (w.take k)).length) ∨
        (∃ (k : ℕ) (hk : k < w.length) (s : ℕ), 0 < s ∧
          s < (expLetters g (w[k]'hk)).length ∧ j = (expWord g (w.take k)).length + s) := by
  intro w
  induction w with
  | nil =>
      intro j hj
      refine Or.inl ⟨0, le_rfl, ?_⟩
      simp only [expWord, List.length_nil] at hj
      simp [expWord]
      omega
  | cons a t ih =>
      intro j hj
      rw [expWord_cons, List.length_append] at hj
      by_cases hja : j ≤ (expLetters g a).length
      · by_cases hj0 : j = 0
        · exact Or.inl ⟨0, by simp, by simp [expWord, hj0]⟩
        · by_cases hjl : j = (expLetters g a).length
          · refine Or.inl ⟨1, by simp, ?_⟩
            simp [expWord, hjl]
          · refine Or.inr ⟨0, by simp, j, by omega, ?_, by simp [expWord]⟩
            simp only [List.getElem_cons_zero]
            omega
      · obtain h | h := ih (j - (expLetters g a).length) (by omega)
        · obtain ⟨k, hk, hjk⟩ := h
          refine Or.inl ⟨k + 1, by simp; omega, ?_⟩
          simp only [List.take_succ_cons, expWord_cons, List.length_append]
          omega
        · obtain ⟨k, hk, s, hs0, hsl, hjk⟩ := h
          refine Or.inr ⟨k + 1, by simp; omega, s, hs0, ?_, ?_⟩
          · simpa using hsl
          · simp only [List.take_succ_cons, expWord_cons, List.length_append]
            omega

/-- **A prefix of the expansion of a cyclic letter spells a power of its generator.** -/
theorem prod_take_expLetters_inr (g : I → Q) (i : I) (e : Q) {s : ℕ}
    (hs : s ≤ (expo g i e).natAbs) :
    ((expLetters g (RelLetter.comp (Sum.inr i) e : RelLetter Q (Sum Lambda I))).take s).prod
      = g i ^ (if 0 ≤ expo g i e then (s : ℤ) else -(s : ℤ)) := by
  simp only [expLetters, List.take_replicate, Nat.min_eq_left hs, List.prod_replicate]
  split_ifs with hnn
  · exact (zpow_natCast (g i) s).symm
  · rw [inv_pow, zpow_neg, zpow_natCast]

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.guessPath_at_letter
#audit_axioms GroupApproximation.GGT.Uncone.guessPath_in_letter
#audit_axioms GroupApproximation.GGT.Uncone.exists_letter_block
#audit_axioms GroupApproximation.GGT.Uncone.prod_take_expLetters_inr
