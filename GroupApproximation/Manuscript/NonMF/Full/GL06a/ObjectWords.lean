import Mathlib.Data.List.Destutter
import Mathlib.Data.List.ReduceOption
import Mathlib.Data.Finset.Card
import GroupApproximation.GGT.VanKampen.ListNoABABLength
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06a: words of objects with gaps

Combinatorics for the object-change count in the proof of Osin's Lemma 9.4
(arXiv:math/0411039v3, §9).  This is infrastructure for `thm:hull` in non_mf_groups_exist.tex; it
certifies no printed sentence on its own.

A polygon reads a word `l : List (Option α)`: `some o` for a side along object `o`, `none` for a
side along no object.

* `changePositions l`: the positions `i` where `l` reads `some a, some b` at `i, i + 1`, `a ≠ b`.
* `reducedWord l`: drop the `none` letters, then merge equal neighbours (`List.destutter`).
* `card_changePositions_le`: `#changePositions l ≤ |reducedWord l| - 1`.
* `noABAB_filterMap_range`: if no four increasing positions read `a, b, a, b` with `a ≠ b`, the
  word `(range n).filterMap g` has no subsequence `a b a b`.
-/

namespace GroupApproximation.Full.GL06a

open GroupApproximation.GGT.VanKampen

variable {α β : Type*}

/-- The word `x :: t` reads two different objects at its first two letters. -/
def headChange [DecidableEq α] : Option α → List (Option α) → Bool
  | some a, some b :: _ => decide (a ≠ b)
  | _, _ => false

theorem headChange_some_some [DecidableEq α] (a b : α) (t : List (Option α)) :
    headChange (some a) (some b :: t) = decide (a ≠ b) := rfl

theorem headChange_none [DecidableEq α] (t : List (Option α)) :
    headChange (none : Option α) t = false := rfl

theorem headChange_some_nil [DecidableEq α] (a : α) :
    headChange (some a) ([] : List (Option α)) = false := rfl

theorem headChange_some_none [DecidableEq α] (a : α) (t : List (Option α)) :
    headChange (some a) (none :: t) = false := rfl

theorem exists_of_headChange [DecidableEq α] {x : Option α} {t : List (Option α)}
    (h : headChange x t = true) : ∃ a b t', x = some a ∧ t = some b :: t' ∧ a ≠ b := by
  cases x with
  | none =>
    rw [headChange_none] at h
    exact absurd h (by decide)
  | some a =>
    cases t with
    | nil =>
      rw [headChange_some_nil] at h
      exact absurd h (by decide)
    | cons y t' =>
      cases y with
      | none =>
        rw [headChange_some_none] at h
        exact absurd h (by decide)
      | some b =>
        rw [headChange_some_some] at h
        exact ⟨a, b, t', rfl, rfl, of_decide_eq_true h⟩

/-- **The change positions of a word**: positions `i` reading `some a, some b` at `i, i + 1`
with `a ≠ b`. -/
def changePositions [DecidableEq α] : List (Option α) → Finset ℕ
  | [] => ∅
  | x :: t =>
    if headChange x t = true then
      insert 0 ((changePositions t).map ⟨Nat.succ, Nat.succ_injective⟩)
    else (changePositions t).map ⟨Nat.succ, Nat.succ_injective⟩

theorem changePositions_nil [DecidableEq α] :
    changePositions ([] : List (Option α)) = ∅ := rfl

theorem changePositions_cons [DecidableEq α] (x : Option α) (t : List (Option α)) :
    changePositions (x :: t) =
      if headChange x t = true then
        insert 0 ((changePositions t).map ⟨Nat.succ, Nat.succ_injective⟩)
      else (changePositions t).map ⟨Nat.succ, Nat.succ_injective⟩ := rfl

/-- Two different objects at `i, i + 1` give a change position. -/
theorem mem_changePositions [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∀ (l : List (Option α)) (i : ℕ), l[i]? = some (some a) → l[i + 1]? = some (some b) →
      i ∈ changePositions l
  | [], i, h1, _ => by
    rw [List.getElem?_nil] at h1
    cases h1
  | x :: t, 0, h1, h2 => by
    rw [List.getElem?_cons_zero] at h1
    rw [List.getElem?_cons_succ] at h2
    obtain rfl : x = some a := Option.some.inj h1
    cases t with
    | nil =>
      rw [List.getElem?_nil] at h2
      cases h2
    | cons y t' =>
      rw [List.getElem?_cons_zero] at h2
      obtain rfl : y = some b := Option.some.inj h2
      have hc : headChange (some a) (some b :: t') = true := decide_eq_true hab
      rw [changePositions_cons, if_pos hc]
      exact Finset.mem_insert_self _ _
  | x :: t, i + 1, h1, h2 => by
    rw [List.getElem?_cons_succ] at h1
    rw [List.getElem?_cons_succ] at h2
    have hi := mem_changePositions hab t i h1 h2
    have hm : i + 1 ∈ (changePositions t).map ⟨Nat.succ, Nat.succ_injective⟩ :=
      Finset.mem_map.mpr ⟨i, hi, rfl⟩
    rw [changePositions_cons]
    by_cases hc : headChange x t = true
    · rw [if_pos hc]
      exact Finset.mem_insert_of_mem hm
    · rw [if_neg hc]
      exact hm

/-- **The reduced word**: drop the `none` letters and merge equal neighbours. -/
def reducedWord [DecidableEq α] (l : List (Option α)) : List α :=
  l.reduceOption.destutter (· ≠ ·)

/-- **At most `|reducedWord l| - 1` change positions.** -/
theorem card_changePositions_le [DecidableEq α] :
    ∀ l : List (Option α), (changePositions l).card ≤ (reducedWord l).length - 1
  | [] => (Finset.card_eq_zero.mpr changePositions_nil).trans_le (Nat.zero_le _)
  | x :: t => by
    have ih := card_changePositions_le t
    rw [changePositions_cons]
    by_cases hc : headChange x t = true
    · rw [if_pos hc]
      obtain ⟨a, b, t', rfl, rfl, hab⟩ := exists_of_headChange hc
      have hlen : (reducedWord (some a :: some b :: t')).length =
          (reducedWord (some b :: t')).length + 1 := by
        simp only [reducedWord, List.reduceOption_cons_of_some]
        rw [List.destutter_cons_cons, if_pos hab, List.length_cons, List.destutter_cons']
      have hpos : 0 < (reducedWord (some b :: t')).length := by
        rw [reducedWord, List.reduceOption_cons_of_some, List.destutter_cons']
        exact List.length_pos_iff.mpr (List.destutter'_ne_nil _ _)
      refine (Finset.card_insert_le _ _).trans ?_
      rw [Finset.card_map]
      omega
    · rw [if_neg hc, Finset.card_map]
      have hle : (reducedWord t).length ≤ (reducedWord (x :: t)).length := by
        cases x with
        | none => exact le_of_eq (by simp only [reducedWord, List.reduceOption_cons_of_none])
        | some a =>
          simp only [reducedWord, List.reduceOption_cons_of_some]
          exact List.length_destutter_ne_le_length_destutter_cons
      omega

/-- The letters of the reduced word are letters of the word. -/
theorem some_mem_of_mem_reducedWord [DecidableEq α] {l : List (Option α)} {a : α}
    (h : a ∈ reducedWord l) : some a ∈ l := by
  have h1 : a ∈ l.reduceOption := (List.destutter_sublist _ _).subset h
  obtain ⟨x, hx, hxa⟩ := List.mem_filterMap.mp h1
  rw [id] at hxa
  rw [← hxa]
  exact hx

/-- A subsequence of `L.filterMap g` lifts to a subsequence of `L`. -/
theorem exists_sublist_map_eq_of_sublist_filterMap (g : β → Option α) :
    ∀ (L : List β) (u : List α), u <+ L.filterMap g →
      ∃ idx : List β, idx <+ L ∧ idx.map g = u.map some
  | [], u, hu => by
    rw [List.filterMap_nil, List.sublist_nil] at hu
    subst hu
    exact ⟨[], List.Sublist.slnil, rfl⟩
  | y :: L, u, hu => by
    cases hy : g y with
    | none =>
      rw [List.filterMap_cons_none hy] at hu
      obtain ⟨idx, hidx, hmap⟩ := exists_sublist_map_eq_of_sublist_filterMap g L u hu
      exact ⟨idx, List.Sublist.cons y hidx, hmap⟩
    | some z =>
      rw [List.filterMap_cons_some hy] at hu
      rcases List.sublist_cons_iff.mp hu with hu' | ⟨r, rfl, hr⟩
      · obtain ⟨idx, hidx, hmap⟩ := exists_sublist_map_eq_of_sublist_filterMap g L u hu'
        exact ⟨idx, List.Sublist.cons y hidx, hmap⟩
      · obtain ⟨idx, hidx, hmap⟩ := exists_sublist_map_eq_of_sublist_filterMap g L r hr
        refine ⟨y :: idx, List.Sublist.cons_cons y hidx, ?_⟩
        rw [List.map_cons, List.map_cons, hy, hmap]

/-- **No `a b a b` in a filtered range word**, from the absence of four increasing positions
reading `a, b, a, b`. -/
theorem noABAB_filterMap_range [DecidableEq α] {g : ℕ → Option α} {n : ℕ}
    (h : ∀ (i1 i2 i3 i4 : ℕ) (a b : α), i1 < i2 → i2 < i3 → i3 < i4 → i4 < n → a ≠ b →
      g i1 = some a → g i2 = some b → g i3 = some a → g i4 = some b → False) :
    ListNoABAB.NoABAB ((List.range n).filterMap g) := by
  intro a b hab habab
  obtain ⟨idx, hidx, hmap⟩ :=
    exists_sublist_map_eq_of_sublist_filterMap g (List.range n) [a, b, a, b] habab
  simp only [List.map_cons, List.map_nil] at hmap
  obtain ⟨i1, t1, rfl, h1, ht1⟩ := List.map_eq_cons_iff.mp hmap
  obtain ⟨i2, t2, rfl, h2, ht2⟩ := List.map_eq_cons_iff.mp ht1
  obtain ⟨i3, t3, rfl, h3, ht3⟩ := List.map_eq_cons_iff.mp ht2
  obtain ⟨i4, t4, rfl, h4, -⟩ := List.map_eq_cons_iff.mp ht3
  have hp := List.Pairwise.sublist hidx List.pairwise_lt_range
  have hp1 := List.pairwise_cons.mp hp
  have hp2 := List.pairwise_cons.mp hp1.2
  have hp3 := List.pairwise_cons.mp hp2.2
  have h12 : i1 < i2 := hp1.1 i2 List.mem_cons_self
  have h23 : i2 < i3 := hp2.1 i3 List.mem_cons_self
  have h34 : i3 < i4 := hp3.1 i4 List.mem_cons_self
  have h4n : i4 < n := List.mem_range.mp (hidx.subset
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  exact h i1 i2 i3 i4 a b h12 h23 h34 h4n hab h1 h2 h3 h4

/-- Reducing a mapped word is filtering the original word. -/
theorem reduceOption_map (g : β → Option α) (L : List β) :
    (L.map g).reduceOption = L.filterMap g :=
  List.filterMap_map

end GroupApproximation.Full.GL06a

#audit_axioms GroupApproximation.Full.GL06a.card_changePositions_le
#audit_axioms GroupApproximation.Full.GL06a.noABAB_filterMap_range
