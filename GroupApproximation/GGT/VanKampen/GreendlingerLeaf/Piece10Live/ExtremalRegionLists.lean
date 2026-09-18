import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# Filtering a walk along closed stretches

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-14.

Pure list combinatorics for `Piece10Live/ExtremalRegion`.  A list `c` is a chain for the
relation `f d = g e` (for darts: `vertexOf (alpha d) = vertexOf e`, a walk).  Filter it by a
predicate `p`.  Between two consecutive kept entries `d`, `e` lies a removed stretch `B`.  If
every such stretch is closed (`g` of its first entry equals `f` of its last entry), the filtered
list is again a chain:

* `rel_of_isChain_stretch`: in a chain `d :: (B ++ e :: C)` with `B` closed, `f d = g e`.
* `exists_split_of_mem_head?_filter`: the head of `t.filter p` splits `t` as `B ++ y :: C` with
  nothing of `B` kept and `y` kept.
* `isChain_filter_of_closedStretches`: the filter of a chain along closed stretches is a chain.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u₁ u₂

section Lists

variable {α : Type u₁} {β : Type u₂}

/-- **A closed stretch between two chain entries links them.** -/
theorem rel_of_isChain_stretch (f g : α → β) {d e : α} {B C : List α}
    (hc : (d :: (B ++ e :: C)).IsChain fun x y => f x = g y)
    (hB : ∀ b₀ ∈ B.head?, ∀ b₁ ∈ B.getLast?, g b₀ = f b₁) :
    f d = g e := by
  obtain ⟨hhead, htail⟩ := List.isChain_cons.mp hc
  cases B with
  | nil => exact hhead e (Option.mem_def.mpr rfl)
  | cons b₀ B' =>
    obtain ⟨b₁, hb₁⟩ : ∃ b₁, (b₀ :: B').getLast? = some b₁ :=
      ⟨_, List.getLast?_eq_getLast (List.cons_ne_nil b₀ B')⟩
    have hmem : b₁ ∈ (b₀ :: B').getLast? := Option.mem_def.mpr hb₁
    exact (hhead b₀ (Option.mem_def.mpr rfl)).trans
      ((hB b₀ (Option.mem_def.mpr rfl) b₁ hmem).trans
        ((List.isChain_append.mp htail).2.2 b₁ hmem e (Option.mem_def.mpr rfl)))

/-- **The head of a filtered list** splits the list before its first kept entry. -/
theorem exists_split_of_mem_head?_filter (p : α → Bool) {t : List α} {y : α}
    (hy : y ∈ (t.filter p).head?) :
    ∃ B C : List α, t = B ++ y :: C ∧ (∀ x ∈ B, p x = false) ∧ p y = true := by
  induction t with
  | nil => simp at hy
  | cons x t ih =>
    by_cases hx : p x = true
    · rw [List.filter_cons_of_pos hx] at hy
      have hxy : x = y := by simpa using hy
      exact ⟨[], t, by simp [hxy], fun _ h => by simp at h, by rw [← hxy]; exact hx⟩
    · rw [List.filter_cons_of_neg hx] at hy
      obtain ⟨B, C, hBC, hB, hpy⟩ := ih hy
      refine ⟨x :: B, C, by simp [hBC], ?_, hpy⟩
      intro z hz
      rcases List.mem_cons.mp hz with hzx | hz
      · rw [hzx]
        simpa using hx
      · exact hB z hz

/-- **Filtering a chain along closed stretches gives a chain.** -/
theorem isChain_filter_of_closedStretches (f g : α → β) (p : α → Bool) {c : List α}
    (hc : c.IsChain fun x y => f x = g y)
    (hs : ∀ (A : List α) (d : α) (B : List α) (e : α) (C : List α),
      c = A ++ d :: (B ++ e :: C) → p d = true → p e = true → (∀ x ∈ B, p x = false) →
        ∀ b₀ ∈ B.head?, ∀ b₁ ∈ B.getLast?, g b₀ = f b₁) :
    (c.filter p).IsChain fun x y => f x = g y := by
  induction c with
  | nil => simp
  | cons x t ih =>
    have ih' := ih (List.isChain_cons.mp hc).2
      fun A d B e C h => hs (x :: A) d B e C (by simp [h])
    by_cases hx : p x = true
    · rw [List.filter_cons_of_pos hx]
      refine ih'.cons ?_
      intro y hy
      obtain ⟨B, C, hBC, hB, hpy⟩ := exists_split_of_mem_head?_filter p hy
      have hc' : (x :: (B ++ y :: C)).IsChain fun x y => f x = g y := by
        rw [← hBC]
        exact hc
      exact rel_of_isChain_stretch f g hc' (hs [] x B y C (by simp [hBC]) hx hpy hB)
    · rw [List.filter_cons_of_neg hx]
      exact ih'

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.rel_of_isChain_stretch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.exists_split_of_mem_head?_filter
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.isChain_filter_of_closedStretches
