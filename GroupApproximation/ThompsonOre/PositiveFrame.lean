import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
# Positive frames: the part of Thompson's group `F` used by the shift argument

A `PositiveFrame G` is a family `x : ℕ → G` with Thompson's relations `x_j x_i = x_i x_(j+1)`
for `i < j`, which generates `G`, and whose sorted positive words with equal values are equal.
Thompson's group `F` is the model.

This file derives the facts the shift argument of Guba's Theorem 3.18 uses.
* `PositiveFrame.word_mergeWords`: a product of sorted words is a sorted word, and
  `mem_mergeWords_lt` bounds its letters.
* `PositiveFrame.word_mul_pow`: `w x_0^k = x_0^k φ^k(w)` for a word `w` in the letters `x_(i+1)`.
* `PositiveFrame.exists_pow_mul_word`: every positive word is `x_0^k w` with `w` sorted in the
  letters `x_(i+1)`, and by `pow_mul_word_inj` this form is unique.
* `PositiveFrame.exists_mul_eq_pow_mul_word`: every finite subset of `G` has a right translate
  made of such words, since every element is a fraction `p q⁻¹` of positive words.
-/

namespace GroupApproximation.ThompsonOre

/-- Thompson-type generators of a group: the relations `x_j x_i = x_i x_(j+1)` for `i < j`,
generation, and uniqueness of sorted positive words. -/
structure PositiveFrame (G : Type*) [Group G] where
  /-- The generators `x_0, x_1, …`. -/
  x : ℕ → G
  rel : ∀ i j : ℕ, i < j → x j * x i = x i * x (j + 1)
  closure_eq_top : Subgroup.closure (Set.range x) = ⊤
  sorted_inj : ∀ l₁ l₂ : List ℕ, l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) →
    (l₁.map x).prod = (l₂.map x).prod → l₁ = l₂

/-- Insert a letter into a sorted word, raising it past each smaller letter. -/
def insLetter (j : ℕ) : List ℕ → List ℕ
  | [] => [j]
  | i :: l => if j ≤ i then j :: i :: l else i :: insLetter (j + 1) l

/-- Merge two sorted words; `mergeWords l₁ l₂` has the value of `l₁ ++ l₂`. -/
def mergeWords : List ℕ → List ℕ → List ℕ
  | [], l₂ => l₂
  | j :: l₁, l₂ => insLetter j (mergeWords l₁ l₂)

theorem mem_insLetter : ∀ (l : List ℕ) (j b : ℕ), b ∈ insLetter j l → j ≤ b ∨ b ∈ l
  | [], j, b, h => by
    simp only [insLetter, List.mem_singleton] at h
    exact Or.inl h.symm.le
  | i :: l, j, b, h => by
    by_cases hji : j ≤ i
    · simp only [insLetter, if_pos hji, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl h.symm.le
      · exact Or.inr (List.mem_cons.mpr h)
    · simp only [insLetter, if_neg hji, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · rcases mem_insLetter l (j + 1) b h with h' | h'
        · exact Or.inl (by omega)
        · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem insLetter_sorted : ∀ (l : List ℕ) (j : ℕ), l.Pairwise (· ≤ ·) →
    (insLetter j l).Pairwise (· ≤ ·)
  | [], j, _ => by simp [insLetter]
  | i :: l, j, hl => by
    rw [List.pairwise_cons] at hl
    by_cases hji : j ≤ i
    · rw [insLetter, if_pos hji, List.pairwise_cons, List.pairwise_cons]
      refine ⟨fun b hb => ?_, hl.1, hl.2⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hji
      · exact hji.trans (hl.1 b hb)
    · rw [insLetter, if_neg hji, List.pairwise_cons]
      refine ⟨fun b hb => ?_, insLetter_sorted l (j + 1) hl.2⟩
      rcases mem_insLetter l (j + 1) b hb with h | h
      · omega
      · exact hl.1 b h

theorem length_insLetter : ∀ (l : List ℕ) (j : ℕ), (insLetter j l).length = l.length + 1
  | [], _ => rfl
  | i :: l, j => by
    by_cases hji : j ≤ i
    · simp only [insLetter, if_pos hji, List.length_cons]
    · simp only [insLetter, if_neg hji, List.length_cons, length_insLetter l (j + 1)]

theorem mem_insLetter_lt {B : ℕ} : ∀ (l : List ℕ) (j : ℕ), j + l.length < B →
    (∀ b ∈ l, b < B) → ∀ b ∈ insLetter j l, b < B
  | [], j, hj, _, b, hb => by
    simp only [insLetter, List.mem_singleton] at hb
    simp only [List.length_nil] at hj
    omega
  | i :: l, j, hj, hl, b, hb => by
    simp only [List.length_cons] at hj
    by_cases hji : j ≤ i
    · simp only [insLetter, if_pos hji, List.mem_cons] at hb
      rcases hb with hb | hb
      · omega
      · exact hl b (List.mem_cons.mpr hb)
    · simp only [insLetter, if_neg hji, List.mem_cons] at hb
      rcases hb with hb | hb
      · exact hl b (List.mem_cons.mpr (Or.inl hb))
      · exact mem_insLetter_lt l (j + 1) (by omega)
          (fun c hc => hl c (List.mem_cons.mpr (Or.inr hc))) b hb

theorem mergeWords_sorted : ∀ (l₁ l₂ : List ℕ), l₂.Pairwise (· ≤ ·) →
    (mergeWords l₁ l₂).Pairwise (· ≤ ·)
  | [], _, h => h
  | j :: l₁, l₂, h => insLetter_sorted _ j (mergeWords_sorted l₁ l₂ h)

theorem length_mergeWords : ∀ (l₁ l₂ : List ℕ),
    (mergeWords l₁ l₂).length = l₁.length + l₂.length
  | [], l₂ => by simp [mergeWords]
  | j :: l₁, l₂ => by
    simp only [mergeWords, length_insLetter, length_mergeWords l₁ l₂, List.length_cons]
    omega

theorem mem_mergeWords_lt {B : ℕ} : ∀ (l₁ l₂ : List ℕ),
    (∀ b ∈ l₁, b + l₁.length + l₂.length < B) → (∀ b ∈ l₂, b < B) →
    ∀ b ∈ mergeWords l₁ l₂, b < B
  | [], _, _, h₂, b, hb => h₂ b hb
  | j :: l₁, l₂, h₁, h₂, b, hb => by
    refine mem_insLetter_lt (mergeWords l₁ l₂) j ?_ ?_ b hb
    · rw [length_mergeWords]
      have := h₁ j (List.mem_cons.mpr (Or.inl rfl))
      simp only [List.length_cons] at this
      omega
    · refine mem_mergeWords_lt l₁ l₂ (fun c hc => ?_) h₂
      have := h₁ c (List.mem_cons.mpr (Or.inr hc))
      simp only [List.length_cons] at this
      omega

namespace PositiveFrame

variable {G : Type*} [Group G] (P : PositiveFrame G)

/-- The value `x_(i₁+a) ⋯ x_(i_s+a)` of the word `[i₁, …, i_s]` with its letters raised by `a`. -/
def word (a : ℕ) (l : List ℕ) : G := (l.map fun i => P.x (i + a)).prod

@[simp] theorem word_nil (a : ℕ) : P.word a [] = 1 := by simp [word]

theorem word_cons (a i : ℕ) (l : List ℕ) : P.word a (i :: l) = P.x (i + a) * P.word a l := by
  simp [word]

theorem word_append (a : ℕ) (l₁ l₂ : List ℕ) :
    P.word a (l₁ ++ l₂) = P.word a l₁ * P.word a l₂ := by
  simp [word, List.prod_append]

theorem word_zero (l : List ℕ) : P.word 0 l = (l.map P.x).prod := by simp [word]

theorem word_one (l : List ℕ) : P.word 1 l = ((l.map (· + 1)).map P.x).prod := by
  simp [word, List.map_map, Function.comp_def]

theorem word_insLetter (a : ℕ) : ∀ (l : List ℕ) (j : ℕ),
    P.word a (insLetter j l) = P.x (j + a) * P.word a l
  | [], j => by simp [insLetter, word_cons]
  | i :: l, j => by
    by_cases hji : j ≤ i
    · rw [insLetter, if_pos hji, word_cons]
    · have h := P.rel (i + a) (j + a) (by omega)
      calc P.word a (insLetter j (i :: l)) = P.x (i + a) * (P.x (j + a + 1) * P.word a l) := by
            rw [insLetter, if_neg hji, word_cons, word_insLetter a l (j + 1), Nat.add_right_comm]
        _ = P.x (j + a) * P.word a (i :: l) := by
            rw [← mul_assoc, ← h, word_cons, mul_assoc]

theorem word_mergeWords (a : ℕ) : ∀ (l₁ l₂ : List ℕ),
    P.word a (mergeWords l₁ l₂) = P.word a l₁ * P.word a l₂
  | [], l₂ => by simp [mergeWords]
  | j :: l₁, l₂ => by
    rw [mergeWords, word_insLetter, word_mergeWords a l₁ l₂, word_cons, mul_assoc]

theorem word_add (a k : ℕ) : ∀ l : List ℕ, P.word (a + k) l = P.word a (l.map (· + k))
  | [] => by simp
  | i :: l => by
    rw [List.map_cons, word_cons, word_cons, word_add a k l,
      show i + (a + k) = i + k + a by omega]

theorem word_mul_x_zero {a : ℕ} (ha : 1 ≤ a) : ∀ l : List ℕ,
    P.word a l * P.x 0 = P.x 0 * P.word (a + 1) l
  | [] => by simp
  | i :: l => by
    have h := P.rel 0 (i + a) (by omega)
    calc P.word a (i :: l) * P.x 0 = P.x (i + a) * (P.word a l * P.x 0) := by
          rw [word_cons, mul_assoc]
      _ = P.x (i + a) * P.x 0 * P.word (a + 1) l := by
          rw [word_mul_x_zero ha l, mul_assoc]
      _ = P.x 0 * P.word (a + 1) (i :: l) := by
          rw [h, word_cons, mul_assoc, Nat.add_assoc]

/-- The shift identity `w x_0^k = x_0^k φ^k(w)`. -/
theorem word_mul_pow {a : ℕ} (ha : 1 ≤ a) (l : List ℕ) : ∀ k : ℕ,
    P.word a l * P.x 0 ^ k = P.x 0 ^ k * P.word (a + k) l
  | 0 => by simp
  | k + 1 => by
    calc P.word a l * P.x 0 ^ (k + 1) = (P.word a l * P.x 0 ^ k) * P.x 0 := by
          rw [pow_succ, mul_assoc]
      _ = P.x 0 ^ k * (P.word (a + k) l * P.x 0) := by
          rw [word_mul_pow ha l k, mul_assoc]
      _ = P.x 0 ^ (k + 1) * P.word (a + (k + 1)) l := by
          rw [P.word_mul_x_zero (a := a + k) (by omega) l, ← mul_assoc, ← pow_succ,
            Nat.add_assoc]

/-- Normal forms multiply by merging: `x_0^k₁ w₁ · x_0^k₂ w₂ = x_0^(k₁+k₂) w`, where `w` merges
`φ^k₂(w₁)` into `w₂`. -/
theorem pow_mul_word_mul_pow_mul_word (k₁ k₂ : ℕ) (l₁ l₂ : List ℕ) :
    P.x 0 ^ k₁ * P.word 1 l₁ * (P.x 0 ^ k₂ * P.word 1 l₂) =
      P.x 0 ^ (k₁ + k₂) * P.word 1 (mergeWords (l₁.map (· + k₂)) l₂) := by
  rw [word_mergeWords, ← word_add, ← mul_assoc, mul_assoc (P.x 0 ^ k₁),
    P.word_mul_pow (a := 1) le_rfl, ← mul_assoc, ← pow_add, mul_assoc]

/-- Every positive word is `x_0^k` times a sorted word in the letters `x_(i+1)`. -/
theorem exists_pow_mul_word : ∀ p : List ℕ, ∃ (k : ℕ) (l : List ℕ),
    l.Pairwise (· ≤ ·) ∧ P.word 0 p = P.x 0 ^ k * P.word 1 l
  | [] => ⟨0, [], List.Pairwise.nil, by simp⟩
  | j :: p => by
    obtain ⟨k, l, hl, h⟩ := exists_pow_mul_word p
    cases j with
    | zero =>
      refine ⟨k + 1, l, hl, ?_⟩
      rw [word_cons, Nat.add_zero, h, ← mul_assoc, pow_succ']
    | succ i =>
      refine ⟨k, insLetter (i + k) l, insLetter_sorted l _ hl, ?_⟩
      have h1 : P.x (i + 1) * P.x 0 ^ k = P.x 0 ^ k * P.x (i + k + 1) := by
        have h2 := P.word_mul_pow (a := 1) le_rfl [i] k
        simp only [word_cons, word_nil, mul_one] at h2
        rwa [show i + (1 + k) = i + k + 1 by omega] at h2
      calc P.word 0 ((i + 1) :: p) = P.x (i + 1) * P.x 0 ^ k * P.word 1 l := by
            rw [word_cons, Nat.add_zero, h, mul_assoc]
        _ = P.x 0 ^ k * P.word 1 (insLetter (i + k) l) := by
            rw [h1, word_insLetter, mul_assoc]

/-- The form `x_0^k w`, with `w` sorted in the letters `x_(i+1)`, is unique. -/
theorem pow_mul_word_inj {k₁ k₂ : ℕ} {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· ≤ ·))
    (h₂ : l₂.Pairwise (· ≤ ·)) (h : P.x 0 ^ k₁ * P.word 1 l₁ = P.x 0 ^ k₂ * P.word 1 l₂) :
    k₁ = k₂ ∧ l₁ = l₂ := by
  have hsucc : ∀ l : List ℕ, l.Pairwise (· ≤ ·) → (l.map (· + 1)).Pairwise (· ≤ ·) :=
    fun l hl => List.pairwise_map.mpr (hl.imp fun h => Nat.add_le_add_right h 1)
  have hs : ∀ (k : ℕ) (l : List ℕ), l.Pairwise (· ≤ ·) →
      (List.replicate k 0 ++ l.map (· + 1)).Pairwise (· ≤ ·) := by
    intro k l hl
    rw [List.pairwise_append]
    refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl), hsucc l hl, ?_⟩
    intro a ha b _
    rw [List.eq_of_mem_replicate ha]
    exact Nat.zero_le _
  have hev : ∀ (k : ℕ) (l : List ℕ),
      ((List.replicate k 0 ++ l.map (· + 1)).map P.x).prod = P.x 0 ^ k * P.word 1 l := by
    intro k l
    rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, word_one]
  have hc : ∀ (k : ℕ) (l : List ℕ), (List.replicate k 0 ++ l.map (· + 1)).count 0 = k := by
    intro k l
    rw [List.count_append, List.count_replicate_self, List.count_eq_zero_of_not_mem] <;> simp
  have e1 := P.sorted_inj _ _ (hs k₁ l₁ h₁) (hs k₂ l₂ h₂) (by rw [hev, hev, h])
  have hk : k₁ = k₂ := (hc k₁ l₁).symm.trans ((congrArg (List.count 0) e1).trans (hc k₂ l₂))
  subst hk
  have hw : P.word 1 l₁ = P.word 1 l₂ := mul_left_cancel h
  have e2 := P.sorted_inj (l₁.map (· + 1)) (l₂.map (· + 1)) (hsucc l₁ h₁) (hsucc l₂ h₂)
    (by rw [← word_one, ← word_one, hw])
  exact ⟨rfl, (List.map_injective_iff.mpr fun a b hab => Nat.add_right_cancel hab) e2⟩

theorem inv_x_mul_word (p : List ℕ) : ∀ a : ℕ, ∃ p' q' : List ℕ,
    (P.x a)⁻¹ * P.word 0 p = P.word 0 p' * (P.word 0 q')⁻¹ := by
  induction p with
  | nil => exact fun a => ⟨[], [a], by simp [word_cons]⟩
  | cons b p ih =>
    intro a
    rcases lt_trichotomy a b with hab | rfl | hba
    · have h1 : (P.x a)⁻¹ * P.x b = P.x (b + 1) * (P.x a)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, P.rel a b hab, ← mul_assoc, inv_mul_cancel,
          one_mul]
      obtain ⟨p', q', hp⟩ := ih a
      refine ⟨(b + 1) :: p', q', ?_⟩
      calc (P.x a)⁻¹ * P.word 0 (b :: p) = ((P.x a)⁻¹ * P.x b) * P.word 0 p := by
            rw [word_cons, Nat.add_zero, mul_assoc]
        _ = P.x (b + 1) * ((P.x a)⁻¹ * P.word 0 p) := by rw [h1, mul_assoc]
        _ = P.word 0 ((b + 1) :: p') * (P.word 0 q')⁻¹ := by
            rw [hp, word_cons, Nat.add_zero, mul_assoc]
    · exact ⟨p, [], by simp [word_cons]⟩
    · have h1 : (P.x a)⁻¹ * P.x b = P.x b * (P.x (a + 1))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← P.rel b a hba, ← mul_assoc, inv_mul_cancel,
          one_mul]
      obtain ⟨p', q', hp⟩ := ih (a + 1)
      refine ⟨b :: p', q', ?_⟩
      calc (P.x a)⁻¹ * P.word 0 (b :: p) = ((P.x a)⁻¹ * P.x b) * P.word 0 p := by
            rw [word_cons, Nat.add_zero, mul_assoc]
        _ = P.x b * ((P.x (a + 1))⁻¹ * P.word 0 p) := by rw [h1, mul_assoc]
        _ = P.word 0 (b :: p') * (P.word 0 q')⁻¹ := by
            rw [hp, word_cons, Nat.add_zero, mul_assoc]

/-- Every element is a fraction `p q⁻¹` of positive words. -/
theorem exists_fraction (g : G) : ∃ p q : List ℕ, g = P.word 0 p * (P.word 0 q)⁻¹ := by
  have hg : g ∈ Subgroup.closure (Set.range P.x) := by
    rw [P.closure_eq_top]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨[], [], by simp⟩
  | mul_left y hy z _ ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨p, q, rfl⟩ := ih
    exact ⟨a :: p, q, by rw [word_cons, Nat.add_zero, mul_assoc]⟩
  | inv_mul_cancel y hy z _ ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨p, q, rfl⟩ := ih
    obtain ⟨p', q', h⟩ := P.inv_x_mul_word p a
    exact ⟨p', q ++ q', by rw [← mul_assoc, h, word_append, mul_inv_rev, mul_assoc]⟩

/-- Every finite subset of `G` has a right translate made of positive words. -/
theorem exists_mul_eq_word (S : Finset G) :
    ∃ g : G, ∀ s ∈ S, ∃ p : List ℕ, s * g = P.word 0 p := by
  classical
  refine Finset.induction_on S ⟨1, fun s hs => by simp at hs⟩ ?_
  intro s S _ ih
  obtain ⟨g, hg⟩ := ih
  obtain ⟨p, q, hpq⟩ := P.exists_fraction (s * g)
  refine ⟨g * P.word 0 q, fun t ht => ?_⟩
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact ⟨p, by rw [← mul_assoc, hpq, inv_mul_cancel_right]⟩
  · obtain ⟨pt, hpt⟩ := hg t ht
    exact ⟨pt ++ q, by rw [← mul_assoc, hpt, word_append]⟩

/-- Every finite subset of `G` has a right translate made of elements `x_0^k w`, with `w`
sorted in the letters `x_(i+1)`. -/
theorem exists_mul_eq_pow_mul_word (S : Finset G) : ∃ g : G, ∀ s ∈ S, ∃ (k : ℕ) (l : List ℕ),
    l.Pairwise (· ≤ ·) ∧ s * g = P.x 0 ^ k * P.word 1 l := by
  obtain ⟨g, hg⟩ := P.exists_mul_eq_word S
  refine ⟨g, fun s hs => ?_⟩
  obtain ⟨p, hp⟩ := hg s hs
  obtain ⟨k, l, hl, h⟩ := P.exists_pow_mul_word p
  exact ⟨k, l, hl, hp.trans h⟩

end PositiveFrame

end GroupApproximation.ThompsonOre
