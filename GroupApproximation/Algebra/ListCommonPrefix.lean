import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# The longest common prefix of two lists

`Algebra/TreeLikeHyperbolic.lean` reduces `δ = 0` hyperbolicity of a word metric
to a "common prefix length" satisfying a cancellation identity and an
ultrametric inequality.  For a free group that function is the length of the
longest common prefix of two reduced words, and this module supplies it together
with the three facts the tree-like structure needs:

* `lcp_le_length_left`, `lcp_le_length_right` --- it is bounded by both lengths;
* `take_lcp_left_eq_right` --- the two lists really do agree that far;
* `lcp_drop_ne` --- and they disagree immediately afterwards, which is the
  maximality that makes the concatenation in the free group reduced;
* `lcp_ultra` --- the ultrametric inequality `min (lcp l₁ l₃) (lcp l₂ l₃) ≤
  lcp l₁ l₂`, which is the branching property of a tree.

Nothing here is about groups.
-/

namespace GroupApproximation
namespace ListPrefix

variable {β : Type*} [DecidableEq β]

/-- The length of the longest common prefix of two lists. -/
def lcp : List β → List β → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: l₁, b :: l₂ => if a = b then lcp l₁ l₂ + 1 else 0

@[simp] theorem lcp_nil_left (l : List β) : lcp [] l = 0 := by
  cases l <;> rfl

@[simp] theorem lcp_nil_right (l : List β) : lcp l [] = 0 := by
  cases l <;> rfl

@[simp] theorem lcp_cons_cons (a b : β) (l₁ l₂ : List β) :
    lcp (a :: l₁) (b :: l₂) = if a = b then lcp l₁ l₂ + 1 else 0 := rfl

/-- The common prefix is no longer than the first list. -/
theorem lcp_le_length_left (l₁ l₂ : List β) : lcp l₁ l₂ ≤ l₁.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      rw [lcp_cons_cons]
      split_ifs with hab
      · have h := ih l₂
        simp only [List.length_cons]
        omega
      · exact Nat.zero_le _

/-- The common prefix is no longer than the second list. -/
theorem lcp_le_length_right (l₁ l₂ : List β) : lcp l₁ l₂ ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      rw [lcp_cons_cons]
      split_ifs with hab
      · have h := ih l₂
        simp only [List.length_cons]
        omega
      · exact Nat.zero_le _

/-- The two lists agree on their common prefix. -/
theorem take_lcp_left_eq_right (l₁ l₂ : List β) :
    List.take (lcp l₁ l₂) l₁ = List.take (lcp l₁ l₂) l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      rw [lcp_cons_cons]
      split_ifs with hab
      · subst hab
        rw [List.take_succ_cons, List.take_succ_cons, ih l₂]
      · simp

/-- **Maximality.**  Immediately past the common prefix the two lists disagree.
This is what makes the free-group concatenation below reduced. -/
theorem lcp_drop_ne : ∀ (l₁ l₂ : List β) {a b : β} {A B : List β},
    List.drop (lcp l₁ l₂) l₁ = a :: A → List.drop (lcp l₁ l₂) l₂ = b :: B →
      a ≠ b := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ a b A B ha _
    simp at ha
  | cons c l₁ ih =>
    intro l₂ a b A B ha hb
    cases l₂ with
    | nil => simp at hb
    | cons d l₂ =>
      by_cases hcd : c = d
      · subst hcd
        rw [lcp_cons_cons, if_pos rfl, List.drop_succ_cons] at ha hb
        exact ih l₂ ha hb
      · rw [lcp_cons_cons, if_neg hcd, List.drop_zero] at ha hb
        rw [List.cons.injEq] at ha hb
        rw [← ha.1, ← hb.1]
        exact hcd

/-- **The ultrametric inequality.**  Agreement branches: if `l₃` agrees with
both `l₁` and `l₂` for a while, then `l₁` and `l₂` agree with each other at
least that long. -/
theorem lcp_ultra (l₁ l₂ l₃ : List β) :
    min (lcp l₁ l₃) (lcp l₂ l₃) ≤ lcp l₁ l₂ := by
  induction l₁ generalizing l₂ l₃ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      cases l₃ with
      | nil => simp
      | cons c l₃ =>
        by_cases hac : a = c
        · by_cases hbc : b = c
          · have hab : a = b := hac.trans hbc.symm
            have h := ih l₂ l₃
            simp only [lcp_cons_cons, if_pos hac, if_pos hbc, if_pos hab]
            omega
          · simp only [lcp_cons_cons, if_neg hbc]
            exact (min_le_right _ _).trans (Nat.zero_le _)
        · simp only [lcp_cons_cons, if_neg hac]
          exact (min_le_left _ _).trans (Nat.zero_le _)

end ListPrefix
end GroupApproximation
