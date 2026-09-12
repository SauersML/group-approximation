import GroupApproximation.Sofic.FreeCancellationNesting

/-!
# The cancellation matching, as data

`FreeCancellationNesting` proves that a word dies freely exactly when its
cancellation is nested (`dyck_iff_mk_eq_one`).  That is a *predicate*, and a
predicate cannot be counted.  This file turns it into data: a `DTree` is a word
together with a distinguished non-crossing perfect matching of its letters, one
matched pair per node, and every fact the curvature count needs is a structural
induction over that tree.

## The shape

`DTree β` has two constructors: `nil`, the empty word, and `wrap a b A B`, which
brackets the subtree `A` between the two matched entries `a` and `b` and then
places `B` after them.  So

  `word (wrap a b A B) = a :: (word A ++ b :: word B)`

and the pair `(a, b)` is one node.  Non-crossing is not a side condition here ---
it is forced by the shape, since everything matched inside `A` is bracketed by
`(a, b)` and everything in `B` lies outside it.  That is exactly the geometric
content of "the diagram can be drawn in the plane", carried by an inductive type
rather than by a topology.

## What is proved

* `word_length` and `pairs_length` --- a tree's word is twice as long as its list
  of pairs, so counting pairs and counting letters are the same problem.
* `dyck_word_of_inverseMatched` and `exists_dtree_of_dyck` --- the two directions
  of the correspondence with `Dyck`, hence with `FreeGroup.mk _ = 1`.  A word
  spells the identity **iff** it carries such a tree with mutually inverse
  entries.
* `exists_dtree_of_dyck_map` --- the same over a *decorated* alphabet.  This is
  the form the count consumes: the letters of the word a conjugate-product
  expression spells are labelled by which block they came from --- which relator,
  which conjugator, or the boundary --- and the matching lifts to the labelled
  word unchanged, so every pair knows the two blocks it joins.

Unconditional throughout, and independent of small cancellation.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u

variable {α : Type*}

/-! ## Words carrying a non-crossing matching -/

/-- **A word with a distinguished non-crossing perfect matching.**  Each `wrap`
node is one matched pair `(a, b)` bracketing the subtree `A`, with `B` following
outside it. -/
inductive DTree (β : Type u) : Type u
  | nil : DTree β
  | wrap : β → β → DTree β → DTree β → DTree β

namespace DTree

variable {β : Type u}

/-- The word a tree spells. -/
def word : DTree β → List β
  | nil => []
  | wrap a b A B => a :: (A.word ++ b :: B.word)

/-- The matched pairs of a tree, one per node. -/
def pairs : DTree β → List (β × β)
  | nil => []
  | wrap a b A B => (a, b) :: (A.pairs ++ B.pairs)

@[simp] theorem word_nil : (nil : DTree β).word = [] := rfl

@[simp] theorem word_wrap (a b : β) (A B : DTree β) :
    (wrap a b A B).word = a :: (A.word ++ b :: B.word) := rfl

@[simp] theorem pairs_nil : (nil : DTree β).pairs = [] := rfl

@[simp] theorem pairs_wrap (a b : β) (A B : DTree β) :
    (wrap a b A B).pairs = (a, b) :: (A.pairs ++ B.pairs) := rfl

/-- **Letters and pairs count the same thing.**  Every letter is matched exactly
once, so the word is twice as long as the list of pairs. -/
theorem word_length (T : DTree β) : T.word.length = 2 * T.pairs.length := by
  induction T with
  | nil => rfl
  | wrap a b A B ihA ihB =>
      simp only [word_wrap, pairs_wrap, List.length_cons, List.length_append]
      omega

/-- Each entry of a pair occurs in the word.  The first. -/
theorem fst_mem_word {T : DTree β} {p : β × β} (h : p ∈ T.pairs) : p.1 ∈ T.word := by
  induction T with
  | nil => exact absurd h (by simp)
  | wrap a b A B ihA ihB =>
      rw [pairs_wrap, List.mem_cons] at h
      rw [word_wrap, List.mem_cons]
      rcases h with rfl | h
      · exact Or.inl rfl
      · refine Or.inr ?_
        rcases List.mem_append.mp h with h' | h'
        · exact List.mem_append_left _ (ihA h')
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (ihB h'))

/-- And the second. -/
theorem snd_mem_word {T : DTree β} {p : β × β} (h : p ∈ T.pairs) : p.2 ∈ T.word := by
  induction T with
  | nil => exact absurd h (by simp)
  | wrap a b A B ihA ihB =>
      rw [pairs_wrap, List.mem_cons] at h
      rw [word_wrap, List.mem_cons]
      rcases h with rfl | h
      · exact Or.inr (List.mem_append_right _ (List.mem_cons_self))
      · refine Or.inr ?_
        rcases List.mem_append.mp h with h' | h'
        · exact List.mem_append_left _ (ihA h')
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (ihB h'))

end DTree

/-! ## Matchings of a free-group word -/

/-- Every pair of the tree matches a letter with its formal inverse. -/
def InverseMatched (T : DTree (α × Bool)) : Prop :=
  ∀ p ∈ T.pairs, p.2 = invLetter p.1

/-- A matched tree spells a nested word. -/
theorem dyck_word_of_inverseMatched {T : DTree (α × Bool)} (h : InverseMatched T) :
    Dyck T.word := by
  induction T with
  | nil => exact Dyck.nil
  | wrap a b A B ihA ihB =>
      have hb : b = invLetter a := h (a, b) (by simp)
      have hA : InverseMatched A := by
        intro p hp
        exact h p (by simp [hp])
      have hB : InverseMatched B := by
        intro p hp
        exact h p (by simp [hp])
      rw [DTree.word_wrap, hb]
      exact Dyck.wrap a A.word B.word (ihA hA) (ihB hB)

/-- Conversely, a nested word carries such a tree. -/
theorem exists_dtree_of_dyck {Z : List (α × Bool)} (h : Dyck Z) :
    ∃ T : DTree (α × Bool), T.word = Z ∧ InverseMatched T := by
  induction h with
  | nil => exact ⟨DTree.nil, rfl, by intro p hp; exact absurd hp (by simp)⟩
  | wrap x A B _ _ ihA ihB =>
      obtain ⟨TA, hTA, hMA⟩ := ihA
      obtain ⟨TB, hTB, hMB⟩ := ihB
      refine ⟨DTree.wrap x (invLetter x) TA TB, ?_, ?_⟩
      · rw [DTree.word_wrap, hTA, hTB]
      · intro p hp
        rw [DTree.pairs_wrap, List.mem_cons] at hp
        rcases hp with rfl | hp
        · rfl
        · rcases List.mem_append.mp hp with hp' | hp'
          · exact hMA p hp'
          · exact hMB p hp'

/-- **A word spells the identity exactly when it carries a matching.** -/
theorem exists_dtree_iff_mk_eq_one {Z : List (α × Bool)} :
    (∃ T : DTree (α × Bool), T.word = Z ∧ InverseMatched T) ↔ FreeGroup.mk Z = 1 := by
  constructor
  · rintro ⟨T, rfl, hT⟩
    exact mk_eq_one_of_dyck (dyck_word_of_inverseMatched hT)
  · intro h
    exact exists_dtree_of_dyck (dyck_iff_mk_eq_one.mpr h)

/-! ## Matchings of a labelled word -/

/-- Splitting a word along a split of its image under a map. -/
theorem map_eq_append_cons {β γ : Type*} (ℓ : β → γ) :
    ∀ (Z : List β) (A' B' : List γ) (y : γ), Z.map ℓ = A' ++ (y :: B') →
      ∃ A z B, Z = A ++ (z :: B) ∧ A.map ℓ = A' ∧ ℓ z = y ∧ B.map ℓ = B' := by
  intro Z
  induction Z with
  | nil =>
      intro A' B' y h
      exact absurd h (by simp)
  | cons c Z' ih =>
      intro A' B' y h
      rcases A' with _ | ⟨a, A''⟩
      · rw [List.nil_append, List.map_cons] at h
        simp only [List.cons.injEq] at h
        exact ⟨[], c, Z', rfl, rfl, h.1, h.2⟩
      · rw [List.map_cons, List.cons_append] at h
        simp only [List.cons.injEq] at h
        obtain ⟨hc, h'⟩ := h
        obtain ⟨A, z, B, hZ, hA, hz, hB⟩ := ih A'' B' y h'
        refine ⟨c :: A, z, B, ?_, ?_, hz, hB⟩
        · rw [hZ, List.cons_append]
        · rw [List.map_cons, hA, hc]

/-- **The matching lifts to a labelled word.**  If the letters of `Z` carry
labels and the underlying word spells the identity, then `Z` itself carries a
matching whose pairs are mutually inverse *after* forgetting the labels --- so
every matched pair knows the two labels it joins.

This is the form the count consumes: label each letter by the block it came
from, and the matching tells you which blocks meet, and where. -/
theorem exists_dtree_of_dyck_map {β : Type u} (ℓ : β → α × Bool) :
    ∀ (n : ℕ) (Z : List β), Z.length ≤ n → FreeGroup.mk (Z.map ℓ) = 1 →
      ∃ T : DTree β, T.word = Z ∧ ∀ p ∈ T.pairs, ℓ p.2 = invLetter (ℓ p.1) := by
  intro n
  induction n with
  | zero =>
      intro Z hlen _
      have hZ : Z = [] := List.length_eq_zero_iff.mp (by omega)
      refine ⟨DTree.nil, hZ.symm, ?_⟩
      intro p hp
      exact absurd hp (by simp)
  | succ n ih =>
      intro Z hlen h
      rcases Z with _ | ⟨z, Z'⟩
      · refine ⟨DTree.nil, rfl, ?_⟩
        intro p hp
        exact absurd hp (by simp)
      · rw [List.map_cons] at h
        obtain ⟨A', B', hsplit, hA', hB'⟩ := exists_split h
        obtain ⟨A, z', B, hZ', hAmap, hz', hBmap⟩ :=
          map_eq_append_cons ℓ Z' A' B' (invLetter (ℓ z)) hsplit
        have hlenA : A.length ≤ n := by
          have hl := congrArg List.length hZ'
          simp only [List.length_append, List.length_cons] at hl hlen ⊢
          omega
        have hlenB : B.length ≤ n := by
          have hl := congrArg List.length hZ'
          simp only [List.length_append, List.length_cons] at hl hlen ⊢
          omega
        obtain ⟨TA, hTA, hMA⟩ := ih A hlenA (by rw [hAmap]; exact hA')
        obtain ⟨TB, hTB, hMB⟩ := ih B hlenB (by rw [hBmap]; exact hB')
        refine ⟨DTree.wrap z z' TA TB, ?_, ?_⟩
        · rw [DTree.word_wrap, hTA, hTB, ← hZ']
        · intro p hp
          rw [DTree.pairs_wrap, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hz'
          · rcases List.mem_append.mp hp with hp' | hp'
            · exact hMA p hp'
            · exact hMB p hp'

end SmallCancellationRouter
end GroupApproximation
