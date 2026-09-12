import GroupApproximation.Sofic.NonCrossingMatching
import GroupApproximation.Sofic.GreendlingerNormalForm

/-!
# A matched pair cannot enclose a reduced block

`NonCrossingMatching` turns the cancellation of a word that dies into data: a
`DTree` whose `wrap` nodes are the matched pairs and whose shape carries
non-crossing.  `ConjExprMatching` labels the letters of
`c₁t₁c₁⁻¹ ⋯ cₙtₙcₙ⁻¹ w⁻¹` by the block they came from.  A curvature count over
that object has to know where pairs *cannot* go, and this file proves the basic
exclusion.

## The two statements

`DTree.eq_nil_of_isReduced` --- a tree whose word reads, through any relabelling
`ℓ` to the free alphabet, as a **reduced** word is empty.  The tree makes its
word spell the identity (`NonCrossingMatching.dyck_word_of_inverseMatched` and
`FreeCancellationNesting.mk_eq_one_of_dyck`), and a reduced word spelling the
identity is the empty one.

`DTree.not_wrap_of_isReduced` --- consequently no matched pair can enclose a
block that is read inside a reduced stretch.  If `wrap a b A B` had
`ℓ a :: (A.word ++ [b])` reduced, then `A.word` would be a reduced infix of it,
so `A` would be empty by the first statement, so the stretch would be the
two-letter word `ℓ a`, `invLetter (ℓ a)` --- and that is not reduced.

## What it is for

The letters of `w⁻¹` carry `Block.boundary` and occupy one contiguous stretch of
the labelled word, and `w` is reduced in every statement the gate quantifies
over.  So `not_wrap_of_isReduced` is exactly what forbids a
`boundary`-to-`boundary` pair: the block such a pair would enclose lies inside
the boundary stretch, which is reduced.  Every boundary letter is therefore
matched to a `relator`, `conj` or `stem` letter, which is what makes
"the letters of relator `k` that survive into `w`" a well-defined count.

`DTree.map` is the relabelling itself, with `word_map` and `mem_pairs_map`; it
is what lets the inverse-matching hypothesis be stated over the decorated
alphabet and used over the free one.

Unconditional: no small cancellation, no minimality, no hypothesis on the
expression.  The only input is reducedness of the stretch.
-/

namespace GroupApproximation
namespace SmallCancellationRouter
namespace DTree

universe u v

variable {β : Type u} {γ : Type v} {α : Type*}

/-! ## 1.  Relabelling -/

/-- Relabelling a tree along a map of alphabets.  The shape --- hence the
non-crossing property --- is untouched. -/
def map (f : β → γ) : DTree β → DTree γ
  | nil => nil
  | wrap a b A B => wrap (f a) (f b) (A.map f) (B.map f)

@[simp] theorem word_map (f : β → γ) (T : DTree β) :
    (T.map f).word = T.word.map f := by
  induction T with
  | nil => rfl
  | wrap a b A B ihA ihB =>
      simp only [map, word_wrap, List.map_cons, List.map_append, ihA, ihB]

/-- Every pair of a relabelled tree is the relabelling of a pair. -/
theorem mem_pairs_map {f : β → γ} {T : DTree β} {q : γ × γ}
    (h : q ∈ (T.map f).pairs) : ∃ p ∈ T.pairs, q = (f p.1, f p.2) := by
  induction T with
  | nil => exact absurd h (by simp [map])
  | wrap a b A B ihA ihB =>
      rw [map, pairs_wrap, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨(a, b), by simp, rfl⟩
      · rcases List.mem_append.mp h with h' | h'
        · obtain ⟨p, hp, hq⟩ := ihA h'
          exact ⟨p, by simp [hp], hq⟩
        · obtain ⟨p, hp, hq⟩ := ihB h'
          exact ⟨p, by simp [hp], hq⟩

/-- A tree is empty exactly when its word is. -/
theorem word_eq_nil_iff {T : DTree β} : T.word = [] ↔ T = nil := by
  cases T with
  | nil => simp
  | wrap a b A B => simp [word_wrap]

/-! ## 2.  A reduced stretch carries no matching -/

/-- **A tree whose word reads as a reduced word is empty.**

The matching makes the word spell the identity; a reduced word spelling the
identity is empty; and a tree with an empty word is `nil`.

`ℓ` is arbitrary, so this applies to the labelled words of `ConjExprMatching`
through `Prod.fst` without any compatibility condition. -/
theorem eq_nil_of_isReduced [DecidableEq α] {T : DTree β} {ℓ : β → α × Bool}
    (hmatch : ∀ p ∈ T.pairs, ℓ p.2 = invLetter (ℓ p.1))
    (hred : FreeGroup.IsReduced (T.word.map ℓ)) : T = nil := by
  have hinv : InverseMatched (T.map ℓ) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_pairs_map hq
    exact hmatch p hp
  have hone : FreeGroup.mk (T.word.map ℓ) = 1 := by
    have h := mk_eq_one_of_dyck (dyck_word_of_inverseMatched hinv)
    rwa [word_map] at h
  have hnil : T.word.map ℓ = [] := by
    have hmk : FreeGroup.mk (T.word.map ℓ)
        = FreeGroup.mk ([] : List (α × Bool)) := by
      rw [hone, ← FreeGroup.one_eq_mk]
    have h := FreeGroup.reduce.sound hmk
    rwa [hred.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h
  exact word_eq_nil_iff.mp (List.map_eq_nil_iff.mp hnil)

/-- **No matched pair encloses a reduced stretch.**

If the letters from a pair's opening entry to its closing entry read as a
reduced word, the pair cannot exist: the block it brackets is a reduced infix,
hence empty by `eq_nil_of_isReduced`, leaving the pair's two entries adjacent
and mutually inverse --- which is precisely what reducedness forbids.

This is the exclusion the count runs on.  Applied to the `Block.boundary`
stretch of `ConjExprMatching.labelledWord`, where the word is `invRev w` for the
reduced `w` the gate quantifies over, it says no pair joins two boundary
letters. -/
theorem not_wrap_of_isReduced [DecidableEq α] {a b : β} {A B : DTree β}
    {ℓ : β → α × Bool}
    (hmatch : ∀ p ∈ (wrap a b A B).pairs, ℓ p.2 = invLetter (ℓ p.1))
    (hred : FreeGroup.IsReduced ((a :: (A.word ++ [b])).map ℓ)) : False := by
  have hlist : (a :: (A.word ++ [b])).map ℓ
      = ℓ a :: (A.word.map ℓ ++ [ℓ b]) := by
    simp
  rw [hlist] at hred
  have hA : FreeGroup.IsReduced (A.word.map ℓ) :=
    isReduced_of_infix ⟨[ℓ a], [ℓ b], by simp⟩ hred
  have hAmatch : ∀ p ∈ A.pairs, ℓ p.2 = invLetter (ℓ p.1) := fun p hp =>
    hmatch p (by simp [hp])
  have hAnil : A = nil := eq_nil_of_isReduced hAmatch hA
  have hab : ℓ b = invLetter (ℓ a) := hmatch (a, b) (by simp)
  rw [hAnil] at hred
  simp only [word_nil, List.map_nil, List.nil_append, hab] at hred
  simp [FreeGroup.IsReduced, invLetter] at hred

end DTree
end SmallCancellationRouter
end GroupApproximation
