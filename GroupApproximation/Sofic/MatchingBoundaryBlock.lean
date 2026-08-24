import GroupApproximation.Sofic.MatchingReduced
import GroupApproximation.Sofic.ConjExprMatching

/-!
# The boundary block: where it sits, and that it never cancels against itself

`ConjExprMatching` labels the letters of `c₁t₁c₁⁻¹ ⋯ cₙtₙcₙ⁻¹ · w⁻¹` by the block
they came from, and `MatchingReduced` proves that no matched pair can enclose a
stretch that reads as a reduced word.  The curvature count cannot begin until
those two are joined into a statement about *positions*, and this file is that
join.

## 1.  Where the boundary block is

`labelledWord e w = labelledExpr 0 e ++ tag Block.boundary (invRev w)`, and
`labelledExpr` emits only `conj`, `relator` and `stem`.  So the `boundary`
letters occupy exactly the last `|w|` positions, and that is stated three ways,
because the three are what downstream consumers reach for:

* `take_labelledWord` / `drop_labelledWord` --- the split at `|exprWord e|` is
  exactly the expression part and exactly the boundary part;
* `length_labelledWord` --- the word is `|exprWord e| + |w|` letters long;
* `snd_getElem_labelledWord_eq_boundary_iff` --- position `i` carries
  `Block.boundary` **iff** `|exprWord e| ≤ i`.

The last is the positional form proper: a letter is a boundary letter exactly by
virtue of where it stands.

## 2.  No pair joins two boundary letters

`not_open_of_boundarySuffix` is the general statement, and it is stronger than
what is needed: if the letters satisfying a predicate `P` form a *suffix* of the
tree's word, and that suffix reads as a reduced word, then **no matched pair has
its opening entry in the suffix**.

The argument is the one `MatchingReduced` sets up.  At a node `wrap a b A B`, if
the opening entry `a` satisfied `P` then `a` could not lie in the non-`P` prefix;
`a` heads the word, so the prefix is empty and the *whole* word is the reduced
suffix.  Then `a :: (A.word ++ [b])` is a prefix of a reduced word, and
`DTree.not_wrap_of_isReduced` refutes the node outright.  The recursion into `A`
and `B` needs only that a contiguous subword of `X ++ Y` splits again in the same
shape, which is `exists_split_of_infix`.

`snd_ne_boundary_of_mem_pairs` reads this on `labelledWord e w`: every boundary
letter is a *closing* entry, and in particular

    no matched pair joins two boundary letters  (`not_boundary_pair`),

so every boundary letter is matched to a `relator`, `conj` or `stem` letter
(`exists_ne_boundary_of_mem_pairs`).  That is what makes "the letters of relator
`k` surviving into `w`" a well-defined count.

The only hypothesis is that `w` is reduced.  In particular the relators are
*not* assumed reduced: the boundary exclusion is cheaper than a general
"no block cancels against itself", which would need every block to be spelled by
a reduced word and so would read the relators too.

Unconditional: no small cancellation, no minimality, no metric condition, and
nothing about the expression beyond the matching it carries.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u v

variable {α : Type*}

/-! ## 1.  Which block a letter carries -/

/-- Every letter of a tagged segment carries that tag. -/
theorem snd_eq_of_mem_tag {b : Block} {l : List (α × Bool)}
    {z : (α × Bool) × Block} (h : z ∈ tag b l) : z.2 = b := by
  rw [tag, List.mem_map] at h
  obtain ⟨y, -, hy⟩ := h
  rw [← hy]

/-- The boolean test and the constructor agree. -/
theorem Block.isBoundary_iff {b : Block} : b.isBoundary = true ↔ b = Block.boundary := by
  cases b <;> simp [Block.isBoundary]

/-- No letter of a labelled factor is a boundary letter: a factor emits only
`conj`, `relator` and `stem`. -/
theorem snd_ne_boundary_of_mem_labelledFactor {k : ℕ} {c s : List (α × Bool)}
    {z : (α × Bool) × Block} (h : z ∈ labelledFactor k c s) :
    z.2 ≠ Block.boundary := by
  rw [labelledFactor, List.mem_append] at h
  rcases h with h | h
  · rw [snd_eq_of_mem_tag h]
    exact fun hh => Block.noConfusion hh
  · rw [List.mem_append] at h
    rcases h with h | h
    · rw [snd_eq_of_mem_tag h]
      exact fun hh => Block.noConfusion hh
    · rw [snd_eq_of_mem_tag h]
      exact fun hh => Block.noConfusion hh

/-- **No letter of the expression part is a boundary letter.**  Nearly
definitional, and the half of the positional statement that carries content:
`Block.boundary` occurs in `labelledWord` only where `tag Block.boundary` put
it. -/
theorem snd_ne_boundary_of_mem_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (z : (α × Bool) × Block), z ∈ labelledExpr k e → z.2 ≠ Block.boundary := by
  intro k e
  induction e generalizing k with
  | nil =>
      intro z hz
      rw [labelledExpr_nil] at hz
      exact absurd hz (by simp)
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      intro z hz
      rw [labelledExpr_cons, List.mem_append] at hz
      rcases hz with h | h
      · exact snd_ne_boundary_of_mem_labelledFactor h
      · exact ih (k + 1) z h

/-! ## 2.  Where the boundary block sits -/

/-- The labelled expression has one letter per letter of the word it spells. -/
theorem length_labelledExpr [DecidableEq α] (k : ℕ)
    (e : List (FreeGroup α × List (α × Bool))) :
    (labelledExpr k e).length = (exprWord e).length := by
  rw [← map_fst_labelledExpr k e, List.length_map]

/-- **The labelled word is `|exprWord e| + |w|` letters long.** -/
theorem length_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    (labelledWord e w).length = (exprWord e).length + w.length := by
  rw [labelledWord, List.length_append, length_labelledExpr, length_tag_boundary]

/-- **The first `|exprWord e|` letters are the expression.** -/
theorem take_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    (labelledWord e w).take (exprWord e).length = labelledExpr 0 e := by
  rw [labelledWord, ← length_labelledExpr 0 e, List.take_left]

/-- **The last `|w|` letters are the boundary block.** -/
theorem drop_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    (labelledWord e w).drop (exprWord e).length
      = tag Block.boundary (FreeGroup.invRev w) := by
  rw [labelledWord, ← length_labelledExpr 0 e, List.drop_left]

/-- A position of a concatenation lies in one side or the other, and which one
is decided by the index. -/
theorem mem_of_getElem_append {β : Type u} (l₁ l₂ : List β) (i : ℕ)
    (hi : i < (l₁ ++ l₂).length) :
    ((l₁ ++ l₂)[i]'hi ∈ l₁ ∧ i < l₁.length) ∨
      ((l₁ ++ l₂)[i]'hi ∈ l₂ ∧ l₁.length ≤ i) := by
  rcases lt_or_ge i l₁.length with h | h
  · refine Or.inl ⟨?_, h⟩
    rw [List.getElem_append_left h]
    exact List.getElem_mem h
  · have h2 : i - l₁.length < l₂.length := by
      rw [List.length_append] at hi
      omega
    refine Or.inr ⟨?_, h⟩
    rw [List.getElem_append_right h]
    exact List.getElem_mem h2

/-- **The positional statement.**  Position `i` of the labelled word carries
`Block.boundary` exactly when it lies past the expression part --- that is,
exactly when it is one of the last `|w|` positions.

This is the form the count consumes: being a boundary letter is a property of
*where the letter stands*, not of the letter. -/
theorem snd_getElem_labelledWord_eq_boundary_iff [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) (i : ℕ)
    (hi : i < (labelledWord e w).length) :
    ((labelledWord e w)[i]'hi).2 = Block.boundary ↔ (exprWord e).length ≤ i := by
  have hlen : (labelledExpr 0 e).length = (exprWord e).length :=
    length_labelledExpr 0 e
  rcases mem_of_getElem_append (labelledExpr 0 e)
      (tag Block.boundary (FreeGroup.invRev w)) i hi with ⟨hz, hlt⟩ | ⟨hz, hge⟩
  · constructor
    · intro hb
      exact absurd hb (snd_ne_boundary_of_mem_labelledExpr 0 e _ hz)
    · intro hb
      exfalso
      omega
  · constructor
    · intro _
      omega
    · intro _
      exact snd_eq_of_mem_tag hz

/-! ## 3.  A suffix that is reduced carries no opening entry -/

/-- Membership passes from a contiguous subword to the word. -/
theorem mem_of_mem_infix {β : Type u} {l₁ l₂ : List β} (h : l₁ <:+: l₂)
    {z : β} (hz : z ∈ l₁) : z ∈ l₂ := by
  obtain ⟨s, t, hst⟩ := h
  rw [← hst]
  exact List.mem_append_left _ (List.mem_append_right _ hz)

/-- Contiguous subwords survive a relabelling. -/
theorem infix_map_of_infix {β : Type u} {δ : Type v} (f : β → δ)
    {l₁ l₂ : List β} (h : l₁ <:+: l₂) : l₁.map f <:+: l₂.map f := by
  obtain ⟨s, t, hst⟩ := h
  exact ⟨s.map f, t.map f, by rw [← hst, List.map_append, List.map_append]⟩

/-- **A contiguous subword splits in the same shape.**  If the `P`-letters of
`X ++ Y` are confined to `Y`, then any contiguous subword is again a non-`P`
stretch followed by a piece of `Y`.

This is the only bookkeeping the induction below needs, and it replaces a
positional API on `DTree`: the recursion never mentions indices. -/
theorem exists_split_of_infix {β : Type u} {P : β → Prop} {X Y M : List β}
    (hM : M <:+: X ++ Y) (hX : ∀ z ∈ X, ¬ P z) :
    ∃ X' Y', M = X' ++ Y' ∧ (∀ z ∈ X', ¬ P z) ∧ Y' <:+: Y := by
  obtain ⟨p, q, hpq⟩ := hM
  have hEq : p ++ (M ++ q) = X ++ Y := by
    rw [← hpq, List.append_assoc]
  rcases List.append_eq_append_iff.mp hEq with ⟨Z, hXZ, hMq⟩ | ⟨Z, -, hY⟩
  · rcases List.append_eq_append_iff.mp hMq with ⟨W, hZW, -⟩ | ⟨W, hMZW, hYW⟩
    · refine ⟨M, [], (List.append_nil M).symm, ?_, ⟨[], Y, by simp⟩⟩
      intro z hz
      refine hX z ?_
      rw [hXZ, hZW]
      exact List.mem_append_right _ (List.mem_append_left _ hz)
    · refine ⟨Z, W, hMZW, ?_, ⟨[], q, by simp [hYW]⟩⟩
      intro z hz
      refine hX z ?_
      rw [hXZ]
      exact List.mem_append_right _ hz
  · refine ⟨[], M, rfl, by simp, ⟨Z, q, ?_⟩⟩
    rw [List.append_assoc]
    exact hY.symm

/-- **No matched pair opens inside a reduced suffix.**

Suppose the letters satisfying `P` form a suffix `Y` of the tree's word and `Y`
reads, under `ℓ`, as a reduced word.  Then the opening entry of every matched
pair fails `P`.

At a node `wrap a b A B` the opening entry `a` heads the word, so if it satisfied
`P` the non-`P` prefix would be empty and the whole word would be the reduced
suffix --- making `a :: (A.word ++ [b])` a prefix of a reduced word, which
`DTree.not_wrap_of_isReduced` forbids.  The two recursive calls re-split the
subwords with `exists_split_of_infix`. -/
theorem not_open_of_boundarySuffix [DecidableEq α] {β : Type u}
    {ℓ : β → α × Bool} {P : β → Prop} :
    ∀ (T : DTree β) (X Y : List β), T.word = X ++ Y →
      (∀ z ∈ X, ¬ P z) → (∀ z ∈ Y, P z) →
      FreeGroup.IsReduced (Y.map ℓ) →
      (∀ p ∈ T.pairs, ℓ p.2 = invLetter (ℓ p.1)) →
      ∀ p ∈ T.pairs, ¬ P p.1 := by
  intro T
  induction T with
  | nil =>
      intro _X _Y _hT _hX _hY _hred _hmatch p hp
      exact absurd hp (by simp)
  | wrap a b A B ihA ihB =>
      intro X Y hT hX hY hred hmatch p hp
      have hmatchA : ∀ q ∈ A.pairs, ℓ q.2 = invLetter (ℓ q.1) := fun q hq =>
        hmatch q (by simp [hq])
      have hmatchB : ∀ q ∈ B.pairs, ℓ q.2 = invLetter (ℓ q.1) := fun q hq =>
        hmatch q (by simp [hq])
      have hAinf : A.word <:+: X ++ Y := by
        rw [← hT]
        exact ⟨[a], b :: B.word, by simp⟩
      have hBinf : B.word <:+: X ++ Y := by
        rw [← hT]
        exact ⟨a :: (A.word ++ [b]), [], by simp⟩
      rw [DTree.pairs_wrap, List.mem_cons] at hp
      rcases hp with rfl | hp
      · show ¬ P a
        intro hPa
        have hXnil : X = [] := by
          rcases X with _ | ⟨x, X'⟩
          · rfl
          · exfalso
            rw [DTree.word_wrap, List.cons_append] at hT
            simp only [List.cons.injEq] at hT
            rw [hT.1] at hPa
            exact hX x List.mem_cons_self hPa
        subst hXnil
        rw [List.nil_append] at hT
        have hYmap : Y.map ℓ
            = (a :: (A.word ++ [b])).map ℓ ++ B.word.map ℓ := by
          rw [← hT, DTree.word_wrap]
          simp
        have hMred : FreeGroup.IsReduced ((a :: (A.word ++ [b])).map ℓ) :=
          isReduced_of_infix ⟨[], B.word.map ℓ, by rw [hYmap, List.nil_append]⟩
            hred
        exact DTree.not_wrap_of_isReduced hmatch hMred
      · rcases List.mem_append.mp hp with hp' | hp'
        · obtain ⟨X', Y', hAeq, hX', hY'inf⟩ := exists_split_of_infix hAinf hX
          exact ihA X' Y' hAeq hX' (fun z hz => hY z (mem_of_mem_infix hY'inf hz))
            (isReduced_of_infix (infix_map_of_infix ℓ hY'inf) hred) hmatchA p hp'
        · obtain ⟨X', Y', hBeq, hX', hY'inf⟩ := exists_split_of_infix hBinf hX
          exact ihB X' Y' hBeq hX' (fun z hz => hY z (mem_of_mem_infix hY'inf hz))
            (isReduced_of_infix (infix_map_of_infix ℓ hY'inf) hred) hmatchB p hp'

/-! ## 4.  Read on the expression's own diagram -/

/-- **Every boundary letter is a closing entry.**  The opening entry of a matched
pair of the expression's diagram is never a boundary letter.

The only hypothesis is that `w` is reduced; the relators are not assumed
reduced, and no small cancellation is read. -/
theorem snd_ne_boundary_of_mem_pairs [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, (p.1).2 ≠ Block.boundary := by
  refine not_open_of_boundarySuffix (ℓ := Prod.fst)
    (P := fun z : (α × Bool) × Block => z.2 = Block.boundary) T
    (labelledExpr 0 e) (tag Block.boundary (FreeGroup.invRev w)) ?_ ?_ ?_ ?_
    hmatch
  · rw [hT, labelledWord]
  · intro z hz
    exact snd_ne_boundary_of_mem_labelledExpr 0 e z hz
  · intro z hz
    exact snd_eq_of_mem_tag hz
  · rw [map_fst_tag]
    exact isReduced_invRev_iff.mpr hw

/-- **No matched pair joins two boundary letters.**

The boundary block does not cancel against itself: the stretch a pair with both
ends in it would enclose lies inside `invRev w`, which is reduced.

In diagram language: the boundary of the picture has no chord. -/
theorem not_boundary_pair [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ¬ ((p.1).2 = Block.boundary ∧ (p.2).2 = Block.boundary) :=
  fun p hp h => snd_ne_boundary_of_mem_pairs hw hT hmatch p hp h.1

/-- **The payoff.**  Every matched pair of the expression's diagram has at least
one end outside the boundary block --- namely its opening end.

So a boundary letter is always matched to a `relator`, `conj` or `stem` letter,
and "the letters of relator `k` that survive into `w`" is a well-defined subset
of the `|w|` boundary positions. -/
theorem exists_ne_boundary_of_mem_pairs [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, (p.2).2 = Block.boundary → (p.1).2 ≠ Block.boundary :=
  fun p hp _ => snd_ne_boundary_of_mem_pairs hw hT hmatch p hp

end SmallCancellationRouter
end GroupApproximation
