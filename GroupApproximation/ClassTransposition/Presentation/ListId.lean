import GroupApproximation.ClassTransposition.Presentation.Comb

/-!
# The relations of Fact O hold for lists of boxes

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §2).

The relation families (a)–(d) of the Ore tree presentation, as identities between realizations of
words on an arbitrary list of boxes:
* (a) Coxeter relations for `swapAt`;
* (b) far commutation of splits;
* (d) naturality of swaps and splits;
* the bubble and layer computations used by the colour exchange (c).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-! ### Splitting and swapping inside concatenations -/

theorem splitAt_append_left : ∀ (l l' : List Box) (i p : ℕ), i < l.length →
    splitAt (l ++ l') i p = splitAt l i p ++ l'
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _, _ => by simp [splitAt]
  | E :: l, l', i + 1, p, h => by
    simp only [List.cons_append, splitAt]
    rw [splitAt_append_left l l' i p (by simpa using h)]

theorem swapAt_append_right {α : Type*} (l : List α) : ∀ (l' : List α) (k : ℕ),
    swapAt (l ++ l') (l.length + k) = l ++ swapAt l' k := by
  induction l with
  | nil => intro l' k; simp
  | cons E l ih =>
    intro l' k
    rw [List.cons_append, List.length_cons, show l.length + 1 + k = (l.length + k) + 1 by omega,
      swapAt_succ, ih, List.cons_append]

theorem swapAt_append_left {α : Type*} : ∀ (l l' : List α) (k : ℕ), k + 1 < l.length →
    swapAt (l ++ l') k = swapAt l k ++ l'
  | [], _, _, h => by simp only [List.length_nil] at h; omega
  | [_], _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _, _, 0, _ => rfl
  | E :: F :: l, l', k + 1, h => by
    rw [List.cons_append, swapAt_succ, swapAt_append_left (F :: l) l' k (by simpa using h),
      swapAt_succ, List.cons_append]

/-! ### (a) Coxeter relations for swaps -/

theorem swapAt_swapAt {α : Type*} : ∀ (b : List α) (k : ℕ), swapAt (swapAt b k) k = b
  | [], _ => rfl
  | [_], 0 => rfl
  | _ :: _ :: _, 0 => rfl
  | E :: b, k + 1 => by rw [swapAt_succ, swapAt_succ, swapAt_swapAt b k]

theorem swapAt_braid {α : Type*} : ∀ (b : List α) (k : ℕ), k + 2 < b.length →
    swapAt (swapAt (swapAt b k) (k + 1)) k = swapAt (swapAt (swapAt b (k + 1)) k) (k + 1)
  | [], _, h => by simp only [List.length_nil] at h; omega
  | [_], _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | [_, _], 0, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _ :: _, 0, _ => rfl
  | E :: b, k + 1, h => by
    simp only [swapAt_succ]
    rw [swapAt_braid b k (by simp at h; omega)]

theorem swapAt_far {α : Type*} : ∀ (b : List α) (k l : ℕ), k + 2 ≤ l →
    swapAt (swapAt b k) l = swapAt (swapAt b l) k
  | [], _, _, _ => rfl
  | [_], 0, l, _ => by cases l <;> rfl
  | E :: F :: b, 0, l, h => by
    obtain ⟨l, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
    rfl
  | E :: b, k + 1, l, h => by
    obtain ⟨l, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    simp only [swapAt_succ]
    rw [swapAt_far b k l (by omega)]

/-! ### (b) Far commutation of splits -/

theorem splitAt_splitAt_far (p : ℕ) : ∀ (b : List Box) (i j q : ℕ), i < j →
    splitAt (splitAt b i p) (j + p - 1) q = splitAt (splitAt b j q) i p
  | [], _, _, _, _ => rfl
  | E :: b, 0, j + 1, q, _ => by
    have h := splitAt_append_right (kids E p) b j q
    rw [length_kids] at h
    simp only [splitAt]
    rw [show j + 1 + p - 1 = p + j by omega, h]
  | E :: b, i + 1, j + 1, q, h => by
    simp only [splitAt]
    rw [show j + 1 + p - 1 = (j + p - 1) + 1 by omega]
    simp only [splitAt]
    rw [splitAt_splitAt_far p b i j q (by omega)]
  | _ :: _, _ + 1, 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, 0, _, h => absurd h (lt_irrefl 0)

/-! ### (d) Naturality of swaps and splits -/

theorem splitAt_swapAt_left (p : ℕ) : ∀ (b : List Box) (k i : ℕ), i < k →
    splitAt (swapAt b k) i p = swapAt (splitAt b i p) (k + p - 1)
  | [], _, _, _ => rfl
  | E :: b, k + 1, 0, _ => by
    have h := swapAt_append_right (kids E p) b k
    rw [length_kids] at h
    rw [swapAt_succ]
    simp only [splitAt]
    rw [show k + 1 + p - 1 = p + k by omega, h]
  | E :: b, k + 1, i + 1, h => by
    rw [swapAt_succ]
    simp only [splitAt]
    rw [show k + 1 + p - 1 = (k + p - 1) + 1 by omega, swapAt_succ,
      splitAt_swapAt_left p b k i (by omega)]
  | _ :: _, 0, _, h => absurd h (Nat.not_lt_zero _)

theorem splitAt_swapAt_right (p : ℕ) : ∀ (b : List Box) (k i : ℕ), k + 1 < i →
    splitAt (swapAt b k) i p = swapAt (splitAt b i p) k
  | [], _, _, _ => rfl
  | [_], 0, _ + 1, _ => rfl
  | E :: F :: b, 0, i, h => by
    obtain ⟨i, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    rfl
  | E :: b, k + 1, i, h => by
    obtain ⟨i, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [swapAt_succ]
    simp only [splitAt]
    rw [swapAt_succ, splitAt_swapAt_right p b k i (by omega)]
  | [_], 0, 0, h => absurd h (by omega)

end GroupApproximation.ClassTransposition.Presentation
