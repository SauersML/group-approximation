import GroupApproximation.Sofic.NonCrossingMatching

/-!
# Runs of a matching, and the conjugate shape they force

A curvature count over a cancellation matching needs to see *runs*: maximal
stretches of consecutive letters matched to consecutive letters somewhere else.
A run is what becomes a single edge of the diagram, and --- when both of its ends
lie in relators --- it is what `C'(1/6)` bounds, because the two stretches are
one and the same subword read in the two relators.

In `DTree` a run is not a positional notion.  The pair at the root of a tree
occupies the two ends of the word it heads; the pair immediately inside it is
adjacent to *both* of those ends exactly when nothing follows it, that is when
its own right subtree is empty.  So the run below a node is the left spine of
`wrap` nodes with empty right children, and that is `spineTail`.

Getting this wrong is easy and I did once: it is the *inner* node's right child
that has to be empty, not the outer one's.  A pair with something after it still
opens where its parent opens, but it no longer closes where its parent closes ---
the trailing word sits between the two closing letters --- so it heads no run.

## The shape a run forces

`word_eq_spineTail_core`: for every tree,

  `word T = F ++ (core ++ S.reverse)`

where `F` and `S` are the two entries of the run's pairs in order.  Over a free
group the entries of a matched pair are mutually inverse, so `S.reverse` is
`invRev F` and this reads

  `word T = F ++ (core ++ invRev F)`   (`word_eq_conj_of_spineTail`)

--- a run makes the word it heads a **conjugate**, and `mk_core_eq_one` says the
core it brackets spells the identity.  That is the mechanism behind every piece
bound in small cancellation theory, isolated here with no relators, no metric
condition and no diagram.

Unconditional throughout.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u

variable {α : Type*}

namespace DTree

variable {β : Type u}

/-! ## The run below a node -/

/-- **The run headed by a tree's root**, when that root is itself part of a run:
descend left through `wrap` nodes as long as nothing follows them, collecting the
matched pairs.  A node with a nonempty right child closes too early to belong to
the run above it, so the descent stops there. -/
def spineTail : DTree β → List (β × β)
  | nil => []
  | wrap a b A nil => (a, b) :: spineTail A
  | wrap _ _ _ (wrap _ _ _ _) => []

/-- **The run at a node**: the node's own pair, then the run below it.  Whether
the node's pair belongs to a longer run above is the caller's business, which is
why the right child plays no part here. -/
def spineDown : DTree β → List (β × β)
  | nil => []
  | wrap a b A _ => (a, b) :: spineTail A

@[simp] theorem spineTail_nil : (nil : DTree β).spineTail = [] := rfl

@[simp] theorem spineTail_wrap_nil (a b : β) (A : DTree β) :
    (wrap a b A nil).spineTail = (a, b) :: A.spineTail := rfl

@[simp] theorem spineTail_wrap_wrap (a b : β) (A : DTree β) (c d : β)
    (C D : DTree β) : (wrap a b A (wrap c d C D)).spineTail = [] := rfl

@[simp] theorem spineDown_nil : (nil : DTree β).spineDown = [] := rfl

@[simp] theorem spineDown_wrap (a b : β) (A B : DTree β) :
    (wrap a b A B).spineDown = (a, b) :: A.spineTail := rfl

/-- Every pair of a run is a pair of the tree. -/
theorem mem_pairs_of_mem_spineTail {T : DTree β} {p : β × β}
    (h : p ∈ T.spineTail) : p ∈ T.pairs := by
  induction T with
  | nil => exact absurd h (by simp)
  | wrap a b A B ihA _ =>
      cases B with
      | nil =>
          rw [spineTail_wrap_nil, List.mem_cons] at h
          rw [pairs_wrap, List.mem_cons]
          rcases h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (List.mem_append_left _ (ihA h))
      | wrap c d C D =>
          rw [spineTail_wrap_wrap] at h
          exact absurd h (by simp)

/-- The same for the run at a node. -/
theorem mem_pairs_of_mem_spineDown {T : DTree β} {p : β × β}
    (h : p ∈ T.spineDown) : p ∈ T.pairs := by
  cases T with
  | nil => exact absurd h (by simp)
  | wrap a b A B =>
      rw [spineDown_wrap, List.mem_cons] at h
      rw [pairs_wrap, List.mem_cons]
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_append_left _ (mem_pairs_of_mem_spineTail h))

/-! ## What a run does to the word -/

/-- **A run brackets a core.**  The first entries of the run's pairs are the
opening letters of the word, in order; the second entries are its closing
letters, in reverse order; everything else is the core between them. -/
theorem word_eq_spineTail_core (T : DTree β) :
    ∃ core : List β, T.word =
      (T.spineTail.map Prod.fst) ++ (core ++ (T.spineTail.map Prod.snd).reverse) := by
  induction T with
  | nil => exact ⟨[], rfl⟩
  | wrap a b A B ihA _ =>
      cases B with
      | nil =>
          obtain ⟨core, hcore⟩ := ihA
          refine ⟨core, ?_⟩
          rw [word_wrap, word_nil, spineTail_wrap_nil, hcore]
          simp only [List.map_cons, List.reverse_cons, List.cons_append,
            List.append_assoc]
      | wrap c d C D =>
          refine ⟨(wrap a b A (wrap c d C D)).word, ?_⟩
          rw [spineTail_wrap_wrap]
          simp only [List.map_nil, List.reverse_nil, List.nil_append,
            List.append_nil]

/-- The same at a node, with the trailing word named: a run brackets a core, and
whatever followed the node follows the run. -/
theorem word_eq_spineDown_core (a b : β) (A B : DTree β) :
    ∃ core : List β, (wrap a b A B).word =
      ((wrap a b A B).spineDown.map Prod.fst)
        ++ (core ++ (((wrap a b A B).spineDown.map Prod.snd).reverse ++ B.word)) := by
  obtain ⟨core, hcore⟩ := word_eq_spineTail_core A
  refine ⟨core, ?_⟩
  rw [word_wrap, spineDown_wrap, hcore]
  simp only [List.map_cons, List.reverse_cons, List.cons_append, List.append_assoc,
    List.nil_append]

end DTree

/-! ## Over a free group: a run is a conjugation -/

/-- The two entries of a matched pair are mutually inverse, so reading a run's
closing letters backwards inverts its opening letters. -/
theorem reverse_map_snd_spineTail {T : DTree (α × Bool)} (h : InverseMatched T) :
    (T.spineTail.map Prod.snd).reverse
      = FreeGroup.invRev (T.spineTail.map Prod.fst) := by
  have hmap : T.spineTail.map Prod.snd
      = (T.spineTail.map Prod.fst).map invLetter := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro p hp
    exact h p (DTree.mem_pairs_of_mem_spineTail hp)
  rw [hmap]
  rfl

/-- **A run is a conjugation.**  The word a tree spells is its run, then a core,
then the run inverted --- which is exactly the shape whose two ends `C'(1/6)`
compares when the run joins two relators. -/
theorem word_eq_conj_of_spineTail {T : DTree (α × Bool)} (h : InverseMatched T) :
    ∃ core : List (α × Bool), T.word =
      (T.spineTail.map Prod.fst)
        ++ (core ++ FreeGroup.invRev (T.spineTail.map Prod.fst)) := by
  obtain ⟨core, hcore⟩ := T.word_eq_spineTail_core
  exact ⟨core, by rw [hcore, reverse_map_snd_spineTail h]⟩

/-- **What a run brackets spells the identity.**  The run's two sides cancel each
other and the whole word dies, so the core dies on its own. -/
theorem mk_core_eq_one {T : DTree (α × Bool)} (h : InverseMatched T)
    {core F : List (α × Bool)}
    (hw : T.word = F ++ (core ++ FreeGroup.invRev F)) :
    FreeGroup.mk core = 1 := by
  have hone : FreeGroup.mk T.word = 1 :=
    mk_eq_one_of_dyck (dyck_word_of_inverseMatched h)
  rw [hw, mk_append_mul, mk_append_mul, mk_invRev_eq_inv] at hone
  calc
    FreeGroup.mk core = (FreeGroup.mk F)⁻¹ *
        (FreeGroup.mk F * (FreeGroup.mk core * (FreeGroup.mk F)⁻¹)) *
          FreeGroup.mk F := by group
    _ = (FreeGroup.mk F)⁻¹ * 1 * FreeGroup.mk F := by rw [hone]
    _ = 1 := by group

end SmallCancellationRouter
end GroupApproximation
