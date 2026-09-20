import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import GroupApproximation.GGT.VanKampen.ListNoABABLength
import GroupApproximation.Meta.AxiomGuard

open scoped List

/-!
# Object changes of a rich polygon: the word combinatorics

Leaf `OsinLemma94ObjectChangesStatement` of the Greendlinger least-area leaf (Hull Thm 7.1,
through the contact count of Osin's Lemma 9.4, arXiv:math/0411039v3, §9).

## The full proof

Let polygon `k` have `N` sides and let `l = [o_0, …, o_{N-1}]` be the objects across its sides,
`o_s = sideObject (kind k s) : Option (Option (Fin n))`: `some (some j)` for a cell side,
`some none` for a boundary side, `none` for a cutting or short side.

1. *Object changes are letter changes.*  A side `s` is an object change iff `o_s` and
   `o_{(s+1) % N}` are both letters and they differ (`Geometry`/`Proof`).  So every object change
   `s < N - 1` is a position `j` with `l[j] = some a`, `l[j+1] = some b`, `a ≠ b`
   (`IsChangeAt`), and at most one more object change sits at `s = N - 1`.
2. *Compress.*  `compress l` drops the blanks and merges equal neighbours (`push`).  It has no
   equal neighbours (`isChain_compress`), is a sublist of the letters `somes l`
   (`compress_sublist_somes`), and its letters are objects of `l`.
3. *Count.*  `#(change positions of l) ≤ |compress l| - 1` by induction on `l`
   (`card_chgSet_le`): a change at position `0` means `l = some a :: t` with `t` starting with
   `some b`, `b ≠ a`, so `compress t = b :: r` and `compress l = a :: b :: r` is one longer.
4. *No `a b a b`.*  If `a b a b <+ somes l` with `a ≠ b`, then `l` has letters `a, b, a, b` at
   positions `i₁ < i₂ < i₃ < i₄` (`noABAB_somes`).  In the geometry these are four sides whose
   first darts lie at increasing positions of one face walk, with faces across `A, B, A, B`,
   `A ≠ B`, both different from the polygon face; `NeighbourFaces.false_of_interleave` forbids
   this on the planar map `S.diagram`.  So `compress l` has no `a b a b`.
5. *Davenport–Schinzel.*  If `compress l ≠ []`,
   `ListNoABAB.length_add_one_le_two_mul_card` gives `|compress l| + 1 ≤ 2 d'` with `d'` the
   number of letters of `compress l`, and `d' ≤ d_k = #neighbours`.  Then
   `#objectChanges ≤ #changes + 1 ≤ |compress l| ≤ 2 d_k`.
   If `compress l = []` there are no letters, no change position, so `#objectChanges ≤ 1 ≤ 2 d_k`
   (a rich polygon has `d_k ≥ 2`).

Model test (hand).  Objects `a b cut a b cut`: the letters at change positions do not form a
chain, but `compress = a b a b` is a chain, and planarity excludes it.  Objects `a a b a`:
`compress = a b a`, changes at positions `1, 2`, plus the cyclic one at `N - 1` would read
`a → a`, not a change: `2 ≤ 2 ≤ 4`.

This module holds steps 2–4 on words.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges

open GroupApproximation.GGT.VanKampen.ListNoABAB

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- The letters of a word with blanks, the blanks dropped. -/
def somes : List (Option α) → List α
  | [] => []
  | none :: t => somes t
  | some a :: t => a :: somes t

/-- Prepend a letter, merging it with an equal first letter. -/
def push (a : α) : List α → List α
  | [] => [a]
  | b :: r => if a = b then b :: r else a :: b :: r

/-- The letters of a word with blanks, blanks dropped and equal neighbours merged. -/
def compress : List (Option α) → List α
  | [] => []
  | none :: t => compress t
  | some a :: t => push a (compress t)

theorem push_eq_cons (a : α) (w : List α) : ∃ r, push a w = a :: r := by
  cases w with
  | nil => exact ⟨[], rfl⟩
  | cons b r =>
    by_cases h : a = b
    · subst h
      exact ⟨r, by simp [push]⟩
    · exact ⟨b :: r, by simp [push, h]⟩

theorem isChain_push {a : α} {w : List α} (hw : w.IsChain (· ≠ ·)) :
    (push a w).IsChain (· ≠ ·) := by
  cases w with
  | nil => exact List.IsChain.singleton a
  | cons b r =>
    by_cases h : a = b
    · simp only [push, if_pos h]
      exact hw
    · simp only [push, if_neg h]
      exact List.IsChain.cons_cons h hw

theorem push_sublist {a : α} {w v : List α} (h : w <+ v) : push a w <+ a :: v := by
  cases w with
  | nil => exact List.Sublist.cons_cons a (List.nil_sublist v)
  | cons b r =>
    by_cases hab : a = b
    · simp only [push, if_pos hab]
      exact List.Sublist.cons a h
    · simp only [push, if_neg hab]
      exact List.Sublist.cons_cons a h

theorem mem_push {a x : α} {w : List α} (h : x ∈ push a w) : x = a ∨ x ∈ w := by
  cases w with
  | nil =>
    simp only [push, List.mem_singleton] at h
    exact Or.inl h
  | cons b r =>
    by_cases hab : a = b
    · simp only [push, if_pos hab] at h
      exact Or.inr h
    · simp only [push, if_neg hab] at h
      rcases List.mem_cons.mp h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'

theorem length_le_length_push (a : α) (w : List α) : w.length ≤ (push a w).length := by
  cases w with
  | nil => simp [push]
  | cons b r =>
    by_cases h : a = b
    · simp only [push, if_pos h, le_refl]
    · simp only [push, if_neg h, List.length_cons]
      omega

theorem isChain_compress : ∀ l : List (Option α), (compress l).IsChain (· ≠ ·)
  | [] => by simp only [compress, List.IsChain.nil]
  | none :: t => by
    simp only [compress]
    exact isChain_compress t
  | some a :: t => by
    simp only [compress]
    exact isChain_push (isChain_compress t)

theorem compress_sublist_somes : ∀ l : List (Option α), compress l <+ somes l
  | [] => by simp only [compress, somes, List.Sublist.slnil]
  | none :: t => by
    simp only [compress, somes]
    exact compress_sublist_somes t
  | some a :: t => by
    simp only [compress, somes]
    exact push_sublist (compress_sublist_somes t)

theorem some_mem_of_mem_compress {x : α} :
    ∀ {l : List (Option α)}, x ∈ compress l → some x ∈ l
  | [], h => by simp only [compress, List.not_mem_nil] at h
  | none :: t, h => by
    simp only [compress] at h
    exact List.mem_cons_of_mem _ (some_mem_of_mem_compress h)
  | some a :: t, h => by
    simp only [compress] at h
    rcases mem_push h with h' | h'
    · rw [h']
      exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons_of_mem _ (some_mem_of_mem_compress h')

theorem length_compress_le (x : Option α) (t : List (Option α)) :
    (compress t).length ≤ (compress (x :: t)).length := by
  cases x with
  | none => simp only [compress, le_refl]
  | some a =>
    simp only [compress]
    exact length_le_length_push a _

omit [DecidableEq α] in
/-- Position `j` of `l` holds a letter and position `j + 1` a different letter. -/
def IsChangeAt (l : List (Option α)) (j : ℕ) : Prop :=
  ∃ a b, l[j]? = some (some a) ∧ l[j + 1]? = some (some b) ∧ a ≠ b

omit [DecidableEq α] in
open scoped Classical in
/-- The change positions of `l`. -/
noncomputable def chgSet (l : List (Option α)) : Finset ℕ :=
  (Finset.range l.length).filter fun j => IsChangeAt l j

omit [DecidableEq α] in
open scoped Classical in
theorem chgSet_cons_subset (x : Option α) (t : List (Option α)) :
    chgSet (x :: t) ⊆ insert 0 ((chgSet t).image Nat.succ) := by
  intro j hj
  obtain ⟨hjr, hjc⟩ := Finset.mem_filter.mp hj
  cases j with
  | zero => exact Finset.mem_insert_self _ _
  | succ i =>
    have hir : i + 1 < t.length + 1 := by
      have := Finset.mem_range.mp hjr
      simpa only [List.length_cons] using this
    obtain ⟨a, b, ha, hb, hab⟩ := hjc
    rw [List.getElem?_cons_succ] at ha hb
    refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), a, b, ha, hb, hab⟩, rfl⟩)

omit [DecidableEq α] in
theorem card_chgSet_cons_le (x : Option α) (t : List (Option α)) :
    (chgSet (x :: t)).card ≤ (chgSet t).card + 1 :=
  (Finset.card_le_card (chgSet_cons_subset x t)).trans
    ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1))

omit [DecidableEq α] in
theorem card_chgSet_cons_le_of_not_mem {x : Option α} {t : List (Option α)}
    (h0 : 0 ∉ chgSet (x :: t)) : (chgSet (x :: t)).card ≤ (chgSet t).card := by
  have hsub : chgSet (x :: t) ⊆ (chgSet t).image Nat.succ := by
    intro j hj
    rcases Finset.mem_insert.mp (chgSet_cons_subset x t hj) with h | h
    · subst h
      exact absurd hj h0
    · exact h
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

open scoped Classical in
theorem exists_of_zero_mem_chgSet {x : Option α} {t : List (Option α)}
    (h0 : 0 ∈ chgSet (x :: t)) : ∃ a b r, x = some a ∧ compress t = b :: r ∧ a ≠ b := by
  obtain ⟨-, a, b, ha, hb, hab⟩ := Finset.mem_filter.mp h0
  cases t with
  | nil =>
    rw [List.getElem?_cons_succ] at hb
    simp at hb
  | cons y t' =>
    rw [List.getElem?_cons_zero] at ha
    rw [List.getElem?_cons_succ, List.getElem?_cons_zero] at hb
    have hx : x = some a := Option.some.inj ha
    have hy : y = some b := Option.some.inj hb
    subst hx hy
    obtain ⟨r, hr⟩ := push_eq_cons b (compress t')
    have hc : compress (some b :: t') = b :: r := by
      simp only [compress]
      exact hr
    exact ⟨a, b, r, rfl, hc, hab⟩

/-- **The change positions of a word are fewer than the letters of its compression.** -/
theorem card_chgSet_le : ∀ l : List (Option α), (chgSet l).card ≤ (compress l).length - 1
  | [] => by simp [chgSet]
  | x :: t => by
    have ih := card_chgSet_le t
    by_cases h0 : 0 ∈ chgSet (x :: t)
    · have hcons := card_chgSet_cons_le x t
      obtain ⟨a, b, r, rfl, hr, hab⟩ := exists_of_zero_mem_chgSet h0
      have hc : compress (some a :: t) = a :: b :: r := by
        simp only [compress, hr, push, if_neg hab]
      rw [hc]
      rw [hr] at ih
      simp only [List.length_cons] at ih ⊢
      omega
    · have h1 := card_chgSet_cons_le_of_not_mem h0
      have h2 := length_compress_le x t
      omega

omit [DecidableEq α] in
/-- **Splitting at the first letter of a subsequence of the letters.** -/
theorem exists_split_of_cons_sublist_somes {c : α} {u : List α} :
    ∀ {l : List (Option α)}, c :: u <+ somes l →
      ∃ l1 l2, l = l1 ++ some c :: l2 ∧ u <+ somes l2
  | [], h => by simp [somes] at h
  | none :: t, h => by
    simp only [somes] at h
    obtain ⟨l1, l2, rfl, hu⟩ := exists_split_of_cons_sublist_somes h
    exact ⟨none :: l1, l2, rfl, hu⟩
  | some a :: t, h => by
    simp only [somes] at h
    rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, hr'⟩
    · obtain ⟨l1, l2, rfl, hu⟩ := exists_split_of_cons_sublist_somes h'
      exact ⟨some a :: l1, l2, rfl, hu⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
      exact ⟨[], t, rfl, hr'⟩

theorem getElem?_append_cons_self {β : Type*} (A t : List β) (x : β) :
    (A ++ x :: t)[A.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem getElem?_append_cons_add {β : Type*} (A t : List β) (x : β) (j : ℕ) :
    (A ++ x :: t)[A.length + 1 + j]? = t[j]? := by
  have hle : A.length ≤ A.length + 1 + j := by omega
  rw [List.getElem?_append_right hle, show A.length + 1 + j - A.length = j + 1 by omega,
    List.getElem?_cons_succ]

omit [DecidableEq α] in
/-- **No `a b a b` among the letters**, from no four positions reading `a, b, a, b`. -/
theorem noABAB_somes {l : List (Option α)}
    (H : ∀ (i1 i2 i3 i4 : ℕ) (a b : α), i1 < i2 → i2 < i3 → i3 < i4 → a ≠ b →
      l[i1]? = some (some a) → l[i2]? = some (some b) → l[i3]? = some (some a) →
        l[i4]? = some (some b) → False) :
    NoABAB (somes l) := by
  intro a b hab hs
  obtain ⟨A1, l2, rfl, h2⟩ := exists_split_of_cons_sublist_somes hs
  obtain ⟨A2, l3, rfl, h3⟩ := exists_split_of_cons_sublist_somes h2
  obtain ⟨A3, l4, rfl, h4⟩ := exists_split_of_cons_sublist_somes h3
  obtain ⟨A4, l5, rfl, -⟩ := exists_split_of_cons_sublist_somes h4
  refine H A1.length (A1.length + 1 + A2.length) (A1.length + 1 + (A2.length + 1 + A3.length))
    (A1.length + 1 + (A2.length + 1 + (A3.length + 1 + A4.length))) a b (by omega) (by omega)
    (by omega) hab ?_ ?_ ?_ ?_
  · exact getElem?_append_cons_self _ _ _
  · rw [getElem?_append_cons_add, getElem?_append_cons_self]
  · rw [getElem?_append_cons_add, getElem?_append_cons_add, getElem?_append_cons_self]
  · rw [getElem?_append_cons_add, getElem?_append_cons_add, getElem?_append_cons_add,
      getElem?_append_cons_self]

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.card_chgSet_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.noABAB_somes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.isChain_compress
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.compress_sublist_somes
