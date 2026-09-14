import GroupApproximation.GroupTheory.LevelShiftDelta
import Mathlib.Data.Finset.Max

/-!
# Words in the generators of the second choice of `Δ`

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, section "LEF groups", tex l.440–444:

> A word in the β^{±1} and h_γ^{±1} gives ℓ, the levels where f changes, which are the exponent sums of β before the letters
> h_γ^{±1}, and the values of f there as words in E. It is trivial if and only if ℓ = 0 and these values are trivial, so Δ
> has solvable word problem.

This file proves the combinatorial half: the triviality criterion. Letters are `(o, b)` with `o : Option ι`. Here
`(none, true)` is `β`, `(some i, true)` is `h_{s i}`, and `b = false` gives the inverse letter.

* `shiftPair w`: the exponent sum of `β` in `w`, as the pair (raises, lowers), so that `ℓ = tagLevel (shiftPair w)`;
* `hLetters w`: the letters `h_γ^{±1}`, each tagged by the exponent sum of `β` before it (these are the levels where `f`
  changes);
* `valueWord w n`: the tagged letters with tag at most `n`, a word in the generators of `Γ` for `f(n)`;
* `isLevelForm_gValue`: the element of `w` is `fβ^ℓ` with these `f` and `ℓ`;
* `gValue_eq_one_iff_tags`: the element is trivial if and only if `ℓ = 0` and the values at the tags are trivial.
-/

namespace GroupApproximation
namespace LevelShiftDelta

open Equiv

variable {Γ : Type*} [Group Γ] {ι : Type*} (s : ι → Γ)

/-- The value in `Perm (Γ × ℤ)` of a word in the letters `β^{±1}` and `h_{s i}^{±1}`. -/
def gValue : List (Option ι × Bool) → Perm (Γ × ℤ)
  | [] => 1
  | (o, b) :: w => (if b then levelGen s o else (levelGen s o)⁻¹) * gValue w

/-- The value in `Γ` of a word in the letters `s i^{±1}`. -/
def lValue : List (ι × Bool) → Γ
  | [] => 1
  | (i, b) :: w => (if b then s i else (s i)⁻¹) * lValue w

variable {s}

/-- The level `a − b` of a tag `(a, b)`. -/
def tagLevel (p : ℕ × ℕ) : ℤ :=
  (p.1 : ℤ) - p.2

/-- **`ℓ`**, the exponent sum of `β` in `w`, as the pair (raises, lowers) (tex l.441). -/
def shiftPair : List (Option ι × Bool) → ℕ × ℕ
  | [] => (0, 0)
  | (none, true) :: w => ((shiftPair w).1 + 1, (shiftPair w).2)
  | (none, false) :: w => ((shiftPair w).1, (shiftPair w).2 + 1)
  | (some _, _) :: w => shiftPair w

/-- **The letters `h_γ^{±1}` tagged by the exponent sum of `β` before them** (tex l.441–443). -/
def hLetters : List (Option ι × Bool) → List ((ℕ × ℕ) × (ι × Bool))
  | [] => []
  | (none, true) :: w => (hLetters w).map fun p => ((p.1.1 + 1, p.1.2), p.2)
  | (none, false) :: w => (hLetters w).map fun p => ((p.1.1, p.1.2 + 1), p.2)
  | (some i, b) :: w => ((0, 0), (i, b)) :: hLetters w

/-- **The value of `f` at the level `n` as a word in `E`** (tex l.443): the tagged letters with tag at most `n`. -/
def valueWord (w : List (Option ι × Bool)) (n : ℤ) : List (ι × Bool) :=
  (hLetters w).filterMap fun p => if tagLevel p.1 ≤ n then some p.2 else none

theorem lValue_cons (x : ι × Bool) (w : List (ι × Bool)) :
    lValue s (x :: w) = (if x.2 then s x.1 else (s x.1)⁻¹) * lValue s w := by
  obtain ⟨i, b⟩ := x
  rfl

theorem IsLevelForm.congr {g : Perm (Γ × ℤ)} {f f' : ℤ → Γ} {ℓ ℓ' : ℤ} (h : IsLevelForm g f ℓ)
    (hf : ∀ n, f n = f' n) (hℓ : ℓ = ℓ') : IsLevelForm g f' ℓ' := by
  intro x m
  rw [h, hf, hℓ]

theorem isLevelForm_levelShift : IsLevelForm (levelShift Γ) (fun _ => 1) 1 := by
  intro x m
  simp

theorem isLevelForm_levelShift_inv : IsLevelForm (levelShift Γ)⁻¹ (fun _ => 1) (-1) := by
  intro x m
  simp [sub_eq_add_neg]

theorem isLevelForm_levelMul (γ : Γ) : IsLevelForm (levelMul γ) (fun n => if 0 ≤ n then γ else 1) 0 := by
  intro x m
  rw [levelMul_apply, add_zero]
  show (if 0 ≤ m then (γ * x, m) else (x, m)) = ((if 0 ≤ m then γ else 1) * x, m)
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, one_mul]

theorem tagLevel_succ_left (p : ℕ × ℕ) : tagLevel (p.1 + 1, p.2) = tagLevel p + 1 := by
  simp only [tagLevel]
  push_cast
  ring

theorem tagLevel_succ_right (p : ℕ × ℕ) : tagLevel (p.1, p.2 + 1) = tagLevel p - 1 := by
  simp only [tagLevel]
  push_cast
  ring

/-- **The element of a word is `fβ^ℓ`** with `ℓ` the exponent sum of `β` and `f(n)` the value of `valueWord w n`
(tex l.440–443). -/
theorem isLevelForm_gValue :
    ∀ w : List (Option ι × Bool),
      IsLevelForm (gValue s w) (fun n => lValue s (valueWord w n)) (tagLevel (shiftPair w))
  | [] => by
    intro x m
    simp [gValue, valueWord, hLetters, lValue, shiftPair, tagLevel]
  | (none, true) :: w => by
    have h := isLevelForm_levelShift.mul (isLevelForm_gValue w)
    refine h.congr (fun n => ?_) ?_
    · rw [one_mul]
      simp only [valueWord, hLetters, List.filterMap_map]
      congr 1
      refine List.filterMap_congr fun p _ => ?_
      simp only [Function.comp_apply, tagLevel_succ_left]
      by_cases hp : tagLevel p.1 ≤ n - 1
      · rw [if_pos hp, if_pos (by linarith)]
      · rw [if_neg hp, if_neg (by linarith)]
    · simp only [shiftPair, tagLevel_succ_left]
      ring
  | (none, false) :: w => by
    have h := isLevelForm_levelShift_inv.mul (isLevelForm_gValue w)
    refine h.congr (fun n => ?_) ?_
    · rw [one_mul]
      simp only [valueWord, hLetters, List.filterMap_map]
      congr 1
      refine List.filterMap_congr fun p _ => ?_
      simp only [Function.comp_apply, tagLevel_succ_right]
      by_cases hp : tagLevel p.1 ≤ n - -1
      · rw [if_pos hp, if_pos (by linarith)]
      · rw [if_neg hp, if_neg (by linarith)]
    · simp only [shiftPair, tagLevel_succ_right]
      ring
  | (some i, true) :: w => by
    have h := (isLevelForm_levelMul (s i)).mul (isLevelForm_gValue w)
    refine h.congr (fun n => ?_) ?_
    · simp only [valueWord, hLetters, List.filterMap_cons, tagLevel, Nat.cast_zero, sub_zero, sub_zero]
      by_cases hn : 0 ≤ n
      · rw [if_pos hn, if_pos hn, lValue_cons]
        rfl
      · rw [if_neg hn, if_neg hn, one_mul]
        rfl
    · simp [shiftPair]
  | (some i, false) :: w => by
    have hinv : gValue s ((some i, false) :: w) = levelMul (s i)⁻¹ * gValue s w := by
      simp only [gValue, levelGen, Bool.false_eq_true, if_false, levelMul_inv]
    rw [hinv]
    have h := (isLevelForm_levelMul (s i)⁻¹).mul (isLevelForm_gValue w)
    refine h.congr (fun n => ?_) ?_
    · simp only [valueWord, hLetters, List.filterMap_cons, tagLevel, Nat.cast_zero, sub_zero]
      by_cases hn : 0 ≤ n
      · rw [if_pos hn, if_pos hn, lValue_cons]
        rfl
      · rw [if_neg hn, if_neg hn, one_mul]
        rfl
    · simp [shiftPair]

/-- A word is trivial if and only if `ℓ = 0` and every value of `f` is trivial. -/
theorem gValue_eq_one_iff (w : List (Option ι × Bool)) :
    gValue s w = 1 ↔ tagLevel (shiftPair w) = 0 ∧ ∀ n, lValue s (valueWord w n) = 1 := by
  have hform := isLevelForm_gValue (s := s) w
  constructor
  · intro h
    rw [h] at hform
    have h1 := hform.levelShiftOf_eq
    have h2 := hform.levelFunOf_eq
    rw [isLevelForm_one.levelShiftOf_eq] at h1
    rw [isLevelForm_one.levelFunOf_eq] at h2
    exact ⟨h1.symm, fun n => (congrFun h2 n).symm⟩
  · rintro ⟨hℓ, hf⟩
    exact hform.ext (isLevelForm_one.congr (fun n => (hf n).symm) hℓ.symm)

/-- **Only the levels where `f` changes matter** (tex l.441–444): if `f` is trivial at every tag, then it is trivial. -/
theorem forall_valueWord_iff (w : List (Option ι × Bool)) :
    (∀ n, lValue s (valueWord w n) = 1) ↔ ∀ p ∈ hLetters w, lValue s (valueWord w (tagLevel p.1)) = 1 := by
  classical
  refine ⟨fun h p _ => h _, fun h n => ?_⟩
  by_cases hT : ∃ p ∈ hLetters w, tagLevel p.1 ≤ n
  · have hne : ((hLetters w).filter fun p => decide (tagLevel p.1 ≤ n)).toFinset.Nonempty := by
      obtain ⟨p, hp, hpn⟩ := hT
      exact ⟨p, List.mem_toFinset.2 (List.mem_filter.2 ⟨hp, by simpa using hpn⟩)⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image _ (fun p => tagLevel p.1) hne
    rw [List.mem_toFinset, List.mem_filter] at hp
    have hpn : tagLevel p.1 ≤ n := by simpa using hp.2
    have hsame : valueWord w n = valueWord w (tagLevel p.1) := by
      unfold valueWord
      refine List.filterMap_congr fun q hq => ?_
      by_cases hqn : tagLevel q.1 ≤ n
      · have hq' := hmax q (List.mem_toFinset.2 (List.mem_filter.2 ⟨hq, by simpa using hqn⟩))
        rw [if_pos hqn, if_pos hq']
      · rw [if_neg hqn, if_neg (by intro hq'; exact hqn (hq'.trans hpn))]
    rw [hsame]
    exact h p hp.1
  · push Not at hT
    have hnil : valueWord w n = [] := by
      unfold valueWord
      rw [List.filterMap_eq_nil_iff]
      intro q hq
      rw [if_neg (not_le.2 (hT q hq))]
    rw [hnil]
    rfl

/-- **A word is trivial if and only if `ℓ = 0` and the values at the levels where `f` changes are trivial**
(tex l.443–444). -/
theorem gValue_eq_one_iff_tags (w : List (Option ι × Bool)) :
    gValue s w = 1 ↔
      (shiftPair w).1 = (shiftPair w).2 ∧ ∀ p ∈ hLetters w, lValue s (valueWord w (tagLevel p.1)) = 1 := by
  rw [gValue_eq_one_iff, forall_valueWord_iff]
  refine and_congr_left' ?_
  simp only [tagLevel]
  omega

end LevelShiftDelta
end GroupApproximation
