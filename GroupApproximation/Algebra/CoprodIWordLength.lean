import Mathlib.GroupTheory.CoprodI

/-!
# Lengths of reduced words under left multiplication

The cyclic-reduction induction for free products
(`Algebra.CoprodITorsionFree`) needs one quantitative fact: multiplying on the
left by a letter from the summand the word *already starts in* does not
increase the length.  That is what makes conjugating by the head letter a
strictly length-decreasing move, and Mathlib has the normal form but not the
length bookkeeping.

Everything here is read off `Word.rcons`, which is `Word.cons` guarded by a
test for the identity: prepending either adds one letter or, when the product
with the old head is trivial, removes one.
-/

namespace GroupApproximation
namespace CoprodIWordLength

open Monoid Monoid.CoprodI

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)]
  [∀ i, DecidableEq (M i)]

/-! ## 1.  `rcons` changes the length by at most one -/

omit [DecidableEq ι] in
theorem le_length_rcons {i : ι} (p : Word.Pair M i) :
    p.tail.toList.length ≤ (Word.rcons p).toList.length := by
  unfold Word.rcons
  split
  · exact le_rfl
  · simp [Word.cons]

omit [DecidableEq ι] in
theorem length_rcons_le {i : ι} (p : Word.Pair M i) :
    (Word.rcons p).toList.length ≤ p.tail.toList.length + 1 := by
  unfold Word.rcons
  split
  · exact Nat.le_succ _
  · simp [Word.cons]

/-! ## 2.  The tail of the pair decomposition -/

theorem rcons_equivPair (i : ι) (w : Word M) :
    Word.rcons (Word.equivPair i w) = w := by
  rw [← Word.equivPair_symm]
  exact (Word.equivPair i).symm_apply_apply w

theorem length_equivPair_tail_le (i : ι) (w : Word M) :
    (Word.equivPair i w).tail.toList.length ≤ w.toList.length := by
  have h := le_length_rcons (Word.equivPair i w)
  rwa [rcons_equivPair] at h

/-- **When the word already starts in `M i`, splitting off the head loses
exactly one letter.** -/
theorem length_eq_of_fstIdx (i : ι) (w : Word M)
    (h : Word.fstIdx w = some i) :
    w.toList.length = (Word.equivPair i w).tail.toList.length + 1 := by
  have hw : Word.rcons (Word.equivPair i w) = w := rcons_equivPair i w
  by_cases hhead : (Word.equivPair i w).head = 1
  · exfalso
    rw [Word.rcons, dif_pos hhead] at hw
    exact (Word.equivPair i w).fstIdx_ne (by rw [hw]; exact h)
  · calc
      w.toList.length = (Word.rcons (Word.equivPair i w)).toList.length := by rw [hw]
      _ = (Word.equivPair i w).tail.toList.length + 1 := by
        rw [Word.rcons, dif_neg hhead]
        simp [Word.cons]

/-! ## 3.  Left multiplication by a letter of the leading summand -/

/-- **Multiplying on the left by a letter of the summand the word already
starts in does not increase the length.**  This is the step that makes
conjugating by the head letter strictly decrease length in the
cyclic-reduction induction. -/
theorem length_smul_le_of_fstIdx {i : ι} (m : M i) (w : Word M)
    (h : Word.fstIdx w = some i) :
    (m • w).toList.length ≤ w.toList.length := by
  rw [Word.smul_def, length_eq_of_fstIdx i w h]
  exact length_rcons_le _

/-- In general the length grows by at most one. -/
theorem length_smul_le {i : ι} (m : M i) (w : Word M) :
    (m • w).toList.length ≤ w.toList.length + 1 := by
  rw [Word.smul_def]
  exact le_trans (length_rcons_le _)
    (Nat.succ_le_succ (length_equivPair_tail_le i w))

end CoprodIWordLength
end GroupApproximation
