import GroupApproximation.Sofic.ConjExprMatching

/-!
# Contracting the stems of the cactus, and what it costs

`ConjExprMatching` labels the letters of

  `labelledWord e w = c₁ t₁ c₁⁻¹ ⋯ cₙ tₙ cₙ⁻¹ · w⁻¹`

by the block each came from, and `exists_dtree_labelledWord` puts a non-crossing
perfect matching on them.  The picture that carries is a **cactus**: `n` discs
joined to a basepoint by stems, the two sides of the `k`-th stem being the
`conj k` and `stem k` letters.  A reduced van Kampen diagram has no stems, so
the curvature count cannot start until the stems are accounted for.

This file supplies the contraction, and settles what it costs.

## 1.  The contraction, as an operation on trees

`DTree.filter` deletes the letters a predicate rejects, rebuilding the tree with
`DTree.append` wherever a deleted pair used to bracket.  `word_filter` is the
theorem:

    the surviving letters carry a non-crossing perfect matching of their own,
    namely `T.filter keep`, whose word is exactly `T.word.filter keep`.

Being a `DTree` at all is the non-crossing half — nesting is forced by the
constructor, not checked — and with `DTree.word_length` the word equation is the
perfect half: the surviving letters are matched in pairs, none left over.
`exists_dtree_diagram` is the reading on the cactus: the relator and boundary
letters carry a matching of the word `t₁ ⋯ tₙ w⁻¹`, every pair still joining a
letter to its formal inverse.

## 2.  The cost, exactly: `PairClosed` is **not** free

The operation has one hypothesis, `PairClosed keep T`: **no matched pair joins a
surviving letter to a deleted one**.  That is not a technicality.  A pair with
one endpoint deleted leaves the other unmatched, so without it there is no
induced matching at all — not a worse one, none.

And it fails.  `mk_relatorWord_of_pairClosed` proves that if the matching of a
labelled word is `PairClosed keepDiagram`, then

    `mk (t₁ ⋯ tₙ) = mk w`,

the relators spelling `w` **with no conjugation whatever**.  Since the whole
point of a conjugate-product expression is that the conjugators are needed, the
hypothesis fails for essentially every expression, and

    **"the stems contract away" is false as stated.**

The smallest witness, over `α = ℕ` with `a = (0, true)` and `b = (1, true)`:
`e = [(a, a⁻¹ b a)]` and `w = b`.  Here `c₁ t₁ c₁⁻¹ = a·a⁻¹ b a·a⁻¹` does spell
`b`, but `t₁ w⁻¹ = a⁻¹ b a b⁻¹` is reduced and nonempty, so it spells nothing
trivial: every matching of `labelledWord e w` must pair a `conj` or `stem` letter
with a `relator` letter.  (Recorded here, not formalized — the theorem above
already refutes the naive statement, for every family at once.)

So a `conj`/`stem` letter can be matched to a relator letter and to a boundary
letter, and the contraction is a genuine hypothesis on the configuration, to be
discharged — or, more likely, replaced by a *fold* that shortens the conjugators
rather than deleting their letters — before the count can run.  What the count
may use for free is `pairClosed_of_forall`: a matching all of whose letters
survive is `PairClosed`, which is why the stem problem disappears exactly when
every conjugator is trivial.

## 3.  What a matched pair is, and where that lives

The companion fact — no matched pair has both of its ends in the same **block** —
is the self-pairing exclusion of the matching lane, proved there from the
interval structure of the blocks and their reducedness, and it is not repeated
here.  What it does *not* say, and what the stem problem needs, is that no pair
has both ends in the same **factor**: `conj k`, `relator k` and `stem k` are
three different blocks of one factor, so a pair joining two of them is allowed by
that theorem and forbidden by `FreeGroup.IsReduced (palindrome cₖ tₖ)`.  The tool
for that strengthening is the factor index in place of the block itself; nothing
here proves it.

Unconditional throughout: no relators, no pieces, no small-cancellation constant.
Nothing here discharges `PairClosed`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u

variable {α : Type*}

namespace DTree

variable {β : Type u}

/-! ## 1.  Placing one matched word after another -/

/-- Concatenating two matchings. -/
def append : DTree β → DTree β → DTree β
  | nil, B => B
  | wrap a b A A', B => wrap a b A (append A' B)

@[simp] theorem nil_append (B : DTree β) : (nil : DTree β).append B = B := rfl

@[simp] theorem wrap_append (a b : β) (A A' B : DTree β) :
    (wrap a b A A').append B = wrap a b A (A'.append B) := rfl

@[simp] theorem word_append (A B : DTree β) :
    (A.append B).word = A.word ++ B.word := by
  induction A with
  | nil => rw [nil_append, word_nil, List.nil_append]
  | wrap a b A₁ A₂ _ihA₁ ihA₂ =>
      rw [wrap_append, word_wrap, word_wrap, ihA₂]
      simp only [List.cons_append, List.append_assoc]

@[simp] theorem pairs_append (A B : DTree β) :
    (A.append B).pairs = A.pairs ++ B.pairs := by
  induction A with
  | nil => rw [nil_append, pairs_nil, List.nil_append]
  | wrap a b A₁ A₂ _ihA₁ ihA₂ =>
      rw [wrap_append, pairs_wrap, pairs_wrap, ihA₂]
      simp only [List.cons_append, List.append_assoc]

/-! ## 2.  Deleting the rejected letters -/

/-- **No matched pair straddles the cut.**  The hypothesis under which deleting
the rejected letters leaves a matching behind. -/
def PairClosed (keep : β → Bool) (T : DTree β) : Prop :=
  ∀ p ∈ T.pairs, keep p.1 = keep p.2

theorem PairClosed.head {keep : β → Bool} {a b : β} {A B : DTree β}
    (h : PairClosed keep (wrap a b A B)) : keep a = keep b :=
  h (a, b) (by simp)

theorem PairClosed.left {keep : β → Bool} {a b : β} {A B : DTree β}
    (h : PairClosed keep (wrap a b A B)) : PairClosed keep A :=
  fun p hp => h p (by simp [hp])

theorem PairClosed.right {keep : β → Bool} {a b : β} {A B : DTree β}
    (h : PairClosed keep (wrap a b A B)) : PairClosed keep B :=
  fun p hp => h p (by simp [hp])

/-- A matching all of whose letters survive is closed for free. -/
theorem pairClosed_of_forall {keep : β → Bool} {T : DTree β}
    (h : ∀ x ∈ T.word, keep x = true) : PairClosed keep T := by
  intro p hp
  rw [h p.1 (fst_mem_word hp), h p.2 (snd_mem_word hp)]

/-- **The contraction.**  A pair both of whose letters survive is kept as a
`wrap`; a pair both of whose letters go is replaced by the concatenation of what
it bracketed with what followed it. -/
def filter (keep : β → Bool) : DTree β → DTree β
  | nil => nil
  | wrap a b A B =>
      if keep a then wrap a b (A.filter keep) (B.filter keep)
      else (A.filter keep).append (B.filter keep)

@[simp] theorem filter_nil (keep : β → Bool) :
    (nil : DTree β).filter keep = nil := rfl

theorem filter_wrap (keep : β → Bool) (a b : β) (A B : DTree β) :
    (wrap a b A B).filter keep =
      if keep a then wrap a b (A.filter keep) (B.filter keep)
      else (A.filter keep).append (B.filter keep) := rfl

/-- A pair of the contracted tree was a pair of the original. -/
theorem mem_pairs_of_mem_pairs_filter {keep : β → Bool} {T : DTree β} {p : β × β}
    (h : p ∈ (T.filter keep).pairs) : p ∈ T.pairs := by
  induction T with
  | nil => exact absurd h (by simp)
  | wrap a b A B ihA ihB =>
      rw [filter_wrap] at h
      rw [pairs_wrap, List.mem_cons]
      cases hka : keep a with
      | false =>
          rw [if_neg (by simp [hka]), pairs_append, List.mem_append] at h
          rcases h with h' | h'
          · exact Or.inr (List.mem_append_left _ (ihA h'))
          · exact Or.inr (List.mem_append_right _ (ihB h'))
      | true =>
          rw [if_pos hka, pairs_wrap, List.mem_cons] at h
          rcases h with rfl | h'
          · exact Or.inl rfl
          · rcases List.mem_append.mp h' with h'' | h''
            · exact Or.inr (List.mem_append_left _ (ihA h''))
            · exact Or.inr (List.mem_append_right _ (ihB h''))

/-- **The surviving letters carry a matching of their own.**  Its word is exactly
the word with the rejected letters struck out; being a `DTree` is the
non-crossing half, and with `word_length` the word equation is the perfect half.

The hypothesis is `PairClosed`, and §2 of the header shows it cannot be
dropped. -/
theorem word_filter (keep : β → Bool) {T : DTree β} (h : PairClosed keep T) :
    (T.filter keep).word = T.word.filter keep := by
  induction T with
  | nil => rfl
  | wrap a b A B ihA ihB =>
      have hab : keep a = keep b := h.head
      have hA := ihA h.left
      have hB := ihB h.right
      cases hka : keep a with
      | false =>
          have hna : ¬ (keep a = true) := by simp [hka]
          have hnb : ¬ (keep b = true) := by rw [← hab]; exact hna
          rw [filter_wrap, if_neg hna, word_append, hA, hB, word_wrap,
            List.filter_cons, if_neg hna, List.filter_append,
            List.filter_cons, if_neg hnb]
      | true =>
          have hkb : keep b = true := by rw [← hab]; exact hka
          rw [filter_wrap, if_pos hka, word_wrap, hA, hB, word_wrap,
            List.filter_cons, if_pos hka, List.filter_append,
            List.filter_cons, if_pos hkb]

end DTree

/-- The contraction of a matching is still matched, letter to formal inverse. -/
theorem matched_filter {β : Type u} {ℓ : β → α × Bool} {keep : β → Bool}
    {T : DTree β} (h : ∀ p ∈ T.pairs, ℓ p.2 = invLetter (ℓ p.1)) :
    ∀ p ∈ (T.filter keep).pairs, ℓ p.2 = invLetter (ℓ p.1) :=
  fun p hp => h p (DTree.mem_pairs_of_mem_pairs_filter hp)

/-- A matching read through a labelling is a nesting of the labelled letters. -/
theorem dyck_map_word {β : Type u} {ℓ : β → α × Bool} :
    ∀ T : DTree β, (∀ p ∈ T.pairs, ℓ p.2 = invLetter (ℓ p.1)) →
      Dyck (T.word.map ℓ) := by
  intro T
  induction T with
  | nil => intro _h; exact Dyck.nil
  | wrap a b A B ihA ihB =>
      intro h
      have hb : ℓ b = invLetter (ℓ a) := h (a, b) (by simp)
      have hA := ihA (fun p hp => h p (by simp [hp]))
      have hB := ihB (fun p hp => h p (by simp [hp]))
      rw [DTree.word_wrap, List.map_cons, List.map_append, List.map_cons, hb]
      exact Dyck.wrap (ℓ a) (A.word.map ℓ) (B.word.map ℓ) hA hB

/-- **The word of a matched tree dies**, read through any labelling: a `DTree` is
a nesting, and a nesting spells the identity. -/
theorem mk_map_word_eq_one {β : Type u} {ℓ : β → α × Bool} {T : DTree β}
    (h : ∀ p ∈ T.pairs, ℓ p.2 = invLetter (ℓ p.1)) :
    FreeGroup.mk (T.word.map ℓ) = 1 :=
  mk_eq_one_of_dyck (dyck_map_word T h)

/-! ## 3.  The stems, named -/

/-- The letters a *diagram* has: the relator letters and the boundary letters.
The two copies of a conjugator — the cactus stems — are exactly what it does
not have. -/
def keepDiagram (x : (α × Bool) × Block) : Bool :=
  x.2.isRelator || x.2.isBoundary

@[simp] theorem tag_nil (b : Block) : tag b ([] : List (α × Bool)) = [] := rfl

@[simp] theorem tag_cons (b : Block) (x : α × Bool) (l : List (α × Bool)) :
    tag b (x :: l) = (x, b) :: tag b l := rfl

theorem filter_tag_pos {b : Block} (hb : (b.isRelator || b.isBoundary) = true)
    (l : List (α × Bool)) : (tag b l).filter keepDiagram = tag b l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [tag_cons, List.filter_cons,
        if_pos (show keepDiagram ((x, b) : (α × Bool) × Block) = true from hb), ih]

theorem filter_tag_neg {b : Block} (hb : (b.isRelator || b.isBoundary) = false)
    (l : List (α × Bool)) : (tag b l).filter keepDiagram = [] := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hx : keepDiagram ((x, b) : (α × Bool) × Block) = false := hb
      rw [tag_cons, List.filter_cons, if_neg (by simp [hx]), ih]

/-- The relators of an expression, concatenated and **unconjugated**. -/
def relatorWord (e : List (FreeGroup α × List (α × Bool))) : List (α × Bool) :=
  (e.map Prod.snd).flatten

@[simp] theorem relatorWord_nil :
    relatorWord ([] : List (FreeGroup α × List (α × Bool))) = [] := rfl

@[simp] theorem relatorWord_cons (x : FreeGroup α) (s : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) :
    relatorWord ((x, s) :: e) = s ++ relatorWord e := rfl

theorem filter_labelledFactor (k : ℕ) (c s : List (α × Bool)) :
    (labelledFactor k c s).filter keepDiagram = tag (Block.relator k) s := by
  rw [labelledFactor, List.filter_append, List.filter_append,
    filter_tag_neg (b := Block.conj k) rfl,
    filter_tag_pos (b := Block.relator k) rfl,
    filter_tag_neg (b := Block.stem k) rfl, List.nil_append, List.append_nil]

theorem map_fst_filter_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      ((labelledExpr k e).filter keepDiagram).map Prod.fst = relatorWord e := by
  intro k e
  induction e generalizing k with
  | nil => rfl
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      rw [labelledExpr_cons, List.filter_append, List.map_append,
        filter_labelledFactor, map_fst_tag, ih (k + 1), relatorWord_cons]

/-- **What the contraction leaves behind, spelled out.**  Striking the stems out
of the labelled word leaves the relators, unconjugated, followed by `w⁻¹`. -/
theorem map_fst_filter_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    ((labelledWord e w).filter keepDiagram).map Prod.fst
      = relatorWord e ++ FreeGroup.invRev w := by
  rw [labelledWord, List.filter_append, List.map_append,
    map_fst_filter_labelledExpr, filter_tag_pos (b := Block.boundary) rfl,
    map_fst_tag]

/-! ## 4.  The obstruction -/

/-- **The stems do not contract for free.**  If no matched pair of the cactus
joined a diagram letter to a stem letter, the relators would already spell `w`
with no conjugation at all.

That conclusion is false for essentially every conjugate-product expression, so
`PairClosed keepDiagram` fails for essentially every one, and "the stems contract
away" is a hypothesis on the configuration rather than a lemma.  The header
records the three-letter witness. -/
theorem mk_relatorWord_of_pairClosed [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    {T : DTree ((α × Bool) × Block)} (hword : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1))
    (hclosed : DTree.PairClosed keepDiagram T) :
    FreeGroup.mk (relatorWord e) = FreeGroup.mk w := by
  have h1 : FreeGroup.mk (((T.filter keepDiagram).word).map Prod.fst) = 1 :=
    mk_map_word_eq_one (matched_filter hmatch)
  rw [DTree.word_filter keepDiagram hclosed, hword, map_fst_filter_labelledWord,
    mk_append_mul, mk_invRev_eq_inv, mul_inv_eq_one] at h1
  exact h1

/-- **The contraction, on the cactus.**  Under `PairClosed keepDiagram` the
relator and boundary letters carry a non-crossing perfect matching of their own,
on the word `t₁ ⋯ tₙ w⁻¹`, with every pair still joining a letter to its formal
inverse.

This is the object the curvature count wants; `mk_relatorWord_of_pairClosed`
says what has to be paid for it. -/
theorem exists_dtree_diagram [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    {T : DTree ((α × Bool) × Block)} (hword : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1))
    (hclosed : DTree.PairClosed keepDiagram T) :
    ∃ S : DTree ((α × Bool) × Block),
      S.word.map Prod.fst = relatorWord e ++ FreeGroup.invRev w ∧
        ∀ p ∈ S.pairs, (p.2).1 = invLetter ((p.1).1) := by
  refine ⟨T.filter keepDiagram, ?_, matched_filter hmatch⟩
  rw [DTree.word_filter keepDiagram hclosed, hword, map_fst_filter_labelledWord]

end SmallCancellationRouter
end GroupApproximation
