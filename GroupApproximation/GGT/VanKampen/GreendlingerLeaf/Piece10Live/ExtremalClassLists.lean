import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal class: list combinatorics

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-15.

Pure list combinatorics for `Piece10Live/ExtremalClass`.

* `closed_stretch_of_rel`: in a chain `d :: (B ++ e :: C)` for the relation `f x = g y`, if the
  two ends are linked (`f d = g e`), the stretch `B` is closed (`g` of its first entry equals `f`
  of its last entry).  This is the converse of
  `P10ExtremalRegion.rel_of_isChain_stretch`.
* `exists_block_of_noGap`: a list in which no two kept entries are separated by a nonempty run of
  removed entries splits as `pre ++ mid ++ post`, with `pre`, `post` removed and `mid` kept.
* `exists_filter_block_of_noGap`: in that case the filter of the list is its infix `mid`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u₁ u₂

section ClassLists

variable {α : Type u₁} {β : Type u₂}

/-- **Linked ends close the stretch between them.** -/
theorem closed_stretch_of_rel (f g : α → β) {d e : α} {B C : List α}
    (hc : (d :: (B ++ e :: C)).IsChain fun x y => f x = g y) (hde : f d = g e) :
    ∀ b₀ ∈ B.head?, ∀ b₁ ∈ B.getLast?, g b₀ = f b₁ := by
  cases B with
  | nil =>
    intro b₀ hb₀
    simp at hb₀
  | cons b B' =>
    intro b₀ hb₀ b₁ hb₁
    obtain ⟨hhead, htail⟩ := List.isChain_cons.mp hc
    have hbb : b = b₀ := Option.some.inj (Option.mem_def.mp hb₀)
    have h₁ : f d = g b := hhead b (Option.mem_def.mpr rfl)
    have h₂ : f b₁ = g e :=
      (List.isChain_append.mp htail).2.2 b₁ hb₁ e (Option.mem_def.mpr rfl)
    rw [← hbb]
    exact h₁.symm.trans (hde.trans h₂.symm)

/-- **No gap gives a block**: kept entries not separated by removed runs form an infix, with only
removed entries before and after. -/
theorem exists_block_of_noGap (p : α → Bool) (l : List α)
    (h : ∀ (A : List α) (d : α) (B : List α) (e : α) (C : List α),
      l = A ++ d :: (B ++ e :: C) → p d = true → p e = true → (∀ x ∈ B, p x = false) →
        B = []) :
    ∃ pre mid post : List α, l = pre ++ mid ++ post ∧ (∀ x ∈ pre, p x = false) ∧
      (∀ x ∈ mid, p x = true) ∧ ∀ x ∈ post, p x = false := by
  induction l with
  | nil =>
    exact ⟨[], [], [], rfl, fun _ hx => by simp at hx, fun _ hx => by simp at hx,
      fun _ hx => by simp at hx⟩
  | cons x t ih =>
    obtain ⟨pre, mid, post, ht, hpre, hmid, hpost⟩ :=
      ih fun A d B e C hl => h (x :: A) d B e C (by simp [hl])
    by_cases hx : p x = true
    · cases pre with
      | nil =>
        refine ⟨[], x :: mid, post, by simp [ht], fun _ hy => by simp at hy, ?_, hpost⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hmid y hy
      | cons y₀ pre' =>
        cases mid with
        | nil =>
          refine ⟨[], [x], (y₀ :: pre') ++ post, by simp [ht], fun _ hy => by simp at hy, ?_, ?_⟩
          · intro y hy
            rw [List.mem_singleton.mp hy]
            exact hx
          · intro y hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hpre y hy
            · exact hpost y hy
        | cons m₀ mid' =>
          exfalso
          have hnil : y₀ :: pre' = [] :=
            h [] x (y₀ :: pre') m₀ (mid' ++ post) (by simp [ht]) hx (hmid m₀ (by simp)) hpre
          exact List.cons_ne_nil _ _ hnil
    · refine ⟨x :: pre, mid, post, by simp [ht], ?_, hmid, hpost⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simpa using hx
      · exact hpre y hy

/-- **No gap gives a filtered block**: the filter of the list is an infix of it. -/
theorem exists_filter_block_of_noGap (p : α → Bool) {l : List α}
    (h : ∀ (A : List α) (d : α) (B : List α) (e : α) (C : List α),
      l = A ++ d :: (B ++ e :: C) → p d = true → p e = true → (∀ x ∈ B, p x = false) →
        B = []) :
    ∃ pre mid post : List α, l = pre ++ mid ++ post ∧ l.filter p = mid := by
  obtain ⟨pre, mid, post, hl, hpre, hmid, hpost⟩ := exists_block_of_noGap p l h
  have h₁ : pre.filter p = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [hpre x hx]
  have h₂ : mid.filter p = mid := List.filter_eq_self.mpr hmid
  have h₃ : post.filter p = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [hpost x hx]
  refine ⟨pre, mid, post, hl, ?_⟩
  rw [hl, List.filter_append, List.filter_append, h₁, h₂, h₃, List.nil_append, List.append_nil]

end ClassLists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.closed_stretch_of_rel
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.exists_block_of_noGap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.exists_filter_block_of_noGap
