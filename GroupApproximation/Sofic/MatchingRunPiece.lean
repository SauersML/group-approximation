import GroupApproximation.Sofic.BlockInfix
import GroupApproximation.Sofic.GreendlingerOverlap

/-!
# What a pair of the matching is worth: self-pairing, and pieces

`ConjExprMatching` builds the object the curvature count runs on — a
non-crossing matching of the letters of `c₁t₁c₁⁻¹ ⋯ cₙtₙcₙ⁻¹ w⁻¹` in which
every matched pair knows which two blocks it joins — and `MatchingSpine`
says what a *run* of that matching does to the word.  Neither file prices a
pair against the relators.  This file prices the two kinds the count has to
charge for:

* a pair joining a relator block to **itself**, and
* a maximal run joining **two** relator blocks.

## 1.  Localisation by the two ends

`BlockInfix.map_fst_infix_of_label` locates a stretch of the labelled word inside
a block when **every** letter of the stretch carries that block's tag.  A matched
pair is not of that kind: its two ends carry the tag and what lies between them
is arbitrary.  So §1 proves the two strip lemmas that read only the *ends*:
`infix_of_infix_append_left` looks at the head, `infix_of_infix_append_right` at
the last letter.  That is the whole of what makes §3 work, and it is why the
self-pairing argument needs no hypothesis about the interior of the bracket.

`BlockAt L b s` packages "the block `b` occupies one contiguous stretch of `L`,
spelling `s`, and nothing outside it carries `b`", and
`blockAt_relator_labelledWord` proves it for every relator block of every
labelled expression — the tags of `labelledExpr j e` carry indices in
`[j, j + |e|)` (`BlockInfix.index_mem_range_of_mem_labelledExpr`), so `relator k`
occurs in one place only.

## 2.  A relator cancels against itself exactly when it is not reduced

`exists_infix_mk_eq_one_of_selfPair` is the characterisation.  A matched pair
with both ends in one block brackets a subtree; the subtree's word dies, the two
ends are mutually inverse, so the whole bracket dies — and the bracket is a
*nonempty* subword of that block's word, because its two ends lie in the block
and blocks are contiguous.  So

    a self-pairing of block `b` ⟹ a nonempty subword of `s` spelling `1`.

`not_selfPair_of_blockAt` is the consequence asked for: a **reduced** block has
no self-pairing, since a nonempty reduced word never spells the identity.  The
relators of a small-cancellation family are reduced — the routing lane carries
`FreeGroup.IsReduced (palindrome c t)`, which gives it — so no relator block of
the matching cancels against its own letters.

Note what is *not* used: minimality of the expression plays no part.  Self-
pairing is refuted one block at a time, by reducedness alone.  And the
characterisation says reducedness is exactly what is spent: drop it and the
configuration is not excluded but exhibited.

## 3.  A run between two relators is a piece

`run_infix_of_blockAt`: a run whose opening letters all carry `relator k` and
whose closing letters all carry `relator l` reads one word `u` twice — `u` as a
subword of `sₖ`, and `invRev u` as a subword of `sₗ`, the inversion coming from
`MatchingSpine.reverse_map_snd_spineTail` (the two ends of a matched pair are
mutually inverse, and the closing letters are read backwards).

`isPiece_of_run_infix` converts that into `IsPiece`, and the orientation is
handled once: `invRev u` is a subword of `invRev sₖ`, which is symmetrized
because `symmetrization` is closed under `invRev`; a subword is a prefix of a
rotation (`exists_rotate_prefix_of_infix`), and `symmetrization` is closed under
rotation.  So `invRev u` prefixes two symmetrized words, which with their
distinctness is exactly `IsPiece`.

Distinctness is a hypothesis, deliberately: it is a statement about the
*expression*, not about the matching, and it is the same statement
`GreendlingerOverlap.isPiece_of_overlap` leaves as a hypothesis.  Here it reads
`∀ i j, (invRev sₖ).rotate i ≠ sₗ.rotate j` — the two relators are not one cyclic
word read in opposite directions.  `six_mul_length_lt_of_relator_run` then states
the bound in the shape the count wants: **six times the number of pairs in the
run is less than the length of the relator it lands in.**

Unconditional except where `MetricSmallCancellation` is named.  Nothing here says
how many runs there are; that is the count, and it is not here.

## Overlap with the lane's other files

`DTree.exists_bracket_of_mem_pairs` below is the same statement as
`MatchingStemContraction.DTree.exists_core_of_mem_pairs`; whichever of the two
lands first, the other should go.  `dyck_word_map_fst` is the label-forgetting
step that the neighbouring files spell with a `DTree.map`; it is proved directly
here so that this file adds no fourth copy of that definition.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u

variable {α : Type*}

/-! ## 1.  Locating a stretch of a word by its two ends -/

/-- **A stretch whose first letter is missing from the left block starts to the
right of it.**  Only the head is looked at, which is what lets this serve the two
ends of a matched pair, whose interior carries no constraint at all.
`BlockInfix.infix_of_forall_ne_left` is the version for a stretch that is
monochromatic throughout. -/
theorem infix_of_infix_append_left {γ : Type*} {A D F' : List γ} {x : γ}
    (h : (x :: F') <:+: A ++ D) (hx : x ∉ A) : (x :: F') <:+: D := by
  induction A with
  | nil => rwa [List.nil_append] at h
  | cons a A ih =>
      rw [List.cons_append] at h
      rcases List.infix_cons_iff.mp h with hpre | hinf
      · obtain ⟨z, hz⟩ := hpre
        simp only [List.cons_append, List.cons.injEq] at hz
        refine absurd ?_ hx
        rw [hz.1]
        exact List.mem_cons_self
      · exact ih hinf (fun hm => hx (List.mem_cons_of_mem a hm))

/-- **And a stretch whose last letter is missing from the right block ends to the
left of it.**  The mirror image, read through `List.reverse_infix`. -/
theorem infix_of_infix_append_right {γ : Type*} {D C F F'' : List γ} {y : γ}
    (h : F <:+: D ++ C) (hrev : F.reverse = y :: F'') (hy : y ∉ C) : F <:+: D := by
  have h1 : F.reverse <:+: (D ++ C).reverse := List.reverse_infix.mpr h
  rw [List.reverse_append, hrev] at h1
  have h2 : (y :: F'') <:+: D.reverse :=
    infix_of_infix_append_left h1 (fun hm => hy (List.mem_reverse.mp hm))
  rw [← hrev] at h2
  exact List.reverse_infix.mp h2

/-! ## 2.  Reduced words do not die -/

/-- A reduced word spelling the identity is empty: its reduction is itself, and
the reduction of the identity is the empty word. -/
theorem eq_nil_of_isReduced_of_mk_eq_one [DecidableEq α] {L : List (α × Bool)}
    (hred : FreeGroup.IsReduced L) (h : FreeGroup.mk L = 1) : L = [] := by
  have h1 : (FreeGroup.mk L).toWord = L := by
    rw [FreeGroup.toWord_mk, hred.reduce_eq]
  rw [h, FreeGroup.toWord_one] at h1
  exact h1.symm

/-! ## 3.  Blocks, as contiguous stretches -/

/-- **The block `b` occupies one contiguous stretch of the labelled word `L`**,
spelling `s`, and nothing outside that stretch carries `b`.  This is all the
location the count needs, and `blockAt_relator_labelledWord` supplies it for
every relator block of every labelled expression. -/
def BlockAt (L : List ((α × Bool) × Block)) (b : Block) (s : List (α × Bool)) :
    Prop :=
  ∃ A₀ C₀ : List ((α × Bool) × Block),
    L = A₀ ++ (tag b s ++ C₀) ∧ (∀ z ∈ A₀, z.2 ≠ b) ∧ (∀ z ∈ C₀, z.2 ≠ b)

/-- A stretch all of whose letters carry `b` lies inside the block `b`, and so
forgets to a subword of the word that block tags. -/
theorem infix_tag_of_forall {b : Block} {s : List (α × Bool)}
    {L F : List ((α × Bool) × Block)}
    (hblock : BlockAt L b s) (hFL : F <:+: L)
    (hall : ∀ z ∈ F, z.2 = b) : F.map Prod.fst <:+: s := by
  obtain ⟨A₀, C₀, hL, hA, hC⟩ := hblock
  rw [hL] at hFL
  exact map_fst_infix_of_label hall hA hC hFL

/-- The labelling of a concatenation is the concatenation of the labellings, with
the factor count carried across. -/
theorem labelledExpr_append [DecidableEq α] :
    ∀ (j : ℕ) (e₁ e₂ : List (FreeGroup α × List (α × Bool))),
      labelledExpr j (e₁ ++ e₂)
        = labelledExpr j e₁ ++ labelledExpr (j + e₁.length) e₂ := by
  intro j e₁
  induction e₁ generalizing j with
  | nil =>
      intro e₂
      rw [List.nil_append, labelledExpr_nil, List.nil_append, List.length_nil,
        Nat.add_zero]
  | cons xs e₁ ih =>
      intro e₂
      obtain ⟨x, s⟩ := xs
      have hidx : j + (e₁.length + 1) = j + 1 + e₁.length := by omega
      rw [List.cons_append, labelledExpr_cons, labelledExpr_cons, ih (j + 1) e₂,
        List.append_assoc, List.length_cons, hidx]

/-- **Every relator block of a labelled expression is contiguous.**  The block
`relator |e₁|` is the relator of the factor at position `|e₁|` and occurs nowhere
else: everything before it carries a smaller factor index or the `conj` tag of
the same factor, everything after carries a larger index, the `stem` tag of the
same factor, or `boundary`. -/
theorem blockAt_relator_labelledWord [DecidableEq α]
    (e₁ e₂ : List (FreeGroup α × List (α × Bool))) (x : FreeGroup α)
    (s w : List (α × Bool)) :
    BlockAt (labelledWord (e₁ ++ (x, s) :: e₂) w) (Block.relator e₁.length) s := by
  refine ⟨labelledExpr 0 e₁ ++ tag (Block.conj e₁.length) x.toWord,
    tag (Block.stem e₁.length) (FreeGroup.invRev x.toWord)
      ++ (labelledExpr (e₁.length + 1) e₂
        ++ tag Block.boundary (FreeGroup.invRev w)), ?_, ?_, ?_⟩
  · simp only [labelledWord, labelledExpr_append, Nat.zero_add,
      labelledExpr_cons, labelledFactor, List.append_assoc]
  · intro z hz hrel
    rw [List.mem_append] at hz
    rcases hz with hz | hz
    · obtain ⟨i, hi1, hi2, hi3⟩ := index_mem_range_of_mem_labelledExpr 0 e₁ z hz
      rw [Nat.zero_add] at hi2
      rcases hi3 with h | h | h
      · rw [h] at hrel
        simp at hrel
      · rw [h] at hrel
        simp at hrel
        omega
      · rw [h] at hrel
        simp at hrel
    · rw [forall_mem_tag _ _ z hz] at hrel
      simp at hrel
  · intro z hz hrel
    rw [List.mem_append, List.mem_append] at hz
    rcases hz with hz | hz | hz
    · rw [forall_mem_tag _ _ z hz] at hrel
      simp at hrel
    · obtain ⟨i, hi1, hi2, hi3⟩ :=
        index_mem_range_of_mem_labelledExpr (e₁.length + 1) e₂ z hz
      rcases hi3 with h | h | h
      · rw [h] at hrel
        simp at hrel
      · rw [h] at hrel
        simp at hrel
        omega
      · rw [h] at hrel
        simp at hrel
    · rw [forall_mem_tag _ _ z hz] at hrel
      simp at hrel

/-- The same, against a split of the expression rather than a concatenation. -/
theorem blockAt_relator_of_split [DecidableEq α]
    {e e₁ e₂ : List (FreeGroup α × List (α × Bool))} {x : FreeGroup α}
    {s w : List (α × Bool)} (hsplit : e = e₁ ++ (x, s) :: e₂) :
    BlockAt (labelledWord e w) (Block.relator e₁.length) s := by
  rw [hsplit]
  exact blockAt_relator_labelledWord e₁ e₂ x s w

/-! ## 4.  The bracket a matched pair spans -/

namespace DTree

variable {β : Type u}

/-- **Every matched pair brackets a subtree.**  The two entries of a pair sit at
the two ends of a contiguous stretch of the word, and what they enclose is the
word of a subtree, whose pairs are pairs of the whole tree.

This is the positional content of non-crossing, read off the inductive shape
rather than off a topology. -/
theorem exists_bracket_of_mem_pairs {T : DTree β} {p : β × β} (h : p ∈ T.pairs) :
    ∃ (X Z : List β) (A : DTree β),
      T.word = X ++ (p.1 :: (A.word ++ (p.2 :: Z))) ∧
        ∀ q ∈ A.pairs, q ∈ T.pairs := by
  induction T with
  | nil => exact absurd h (by simp)
  | wrap a b A B ihA ihB =>
      rw [pairs_wrap, List.mem_cons] at h
      rcases h with rfl | h
      · refine ⟨[], B.word, A, by simp, ?_⟩
        intro q hq
        rw [pairs_wrap, List.mem_cons]
        exact Or.inr (List.mem_append_left _ hq)
      · rcases List.mem_append.mp h with h' | h'
        · obtain ⟨X, Z, A', hw, hsub⟩ := ihA h'
          refine ⟨a :: X, Z ++ (b :: B.word), A', ?_, ?_⟩
          · rw [word_wrap, hw]
            simp only [List.cons_append, List.append_assoc]
          · intro q hq
            rw [pairs_wrap, List.mem_cons]
            exact Or.inr (List.mem_append_left _ (hsub q hq))
        · obtain ⟨X, Z, A', hw, hsub⟩ := ihB h'
          refine ⟨a :: (A.word ++ (b :: X)), Z, A', ?_, ?_⟩
          · rw [word_wrap, hw]
            simp only [List.cons_append, List.append_assoc]
          · intro q hq
            rw [pairs_wrap, List.mem_cons]
            exact Or.inr (List.mem_append_right _ (hsub q hq))

end DTree

/-- **A labelled matching forgets to a nested word.**  Proved directly, so that
this file adds no further copy of `DTree.map`. -/
theorem dyck_word_map_fst [DecidableEq α] (T : DTree ((α × Bool) × Block)) :
    (∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1) →
      Dyck (T.word.map (Prod.fst : (α × Bool) × Block → α × Bool)) := by
  induction T with
  | nil =>
      intro _
      exact Dyck.nil
  | wrap a b A B ihA ihB =>
      intro h
      have hb : b.1 = invLetter a.1 := h (a, b) (by simp)
      have hA : ∀ p ∈ A.pairs, (p.2).1 = invLetter (p.1).1 :=
        fun p hp => h p (by simp [hp])
      have hB : ∀ p ∈ B.pairs, (p.2).1 = invLetter (p.1).1 :=
        fun p hp => h p (by simp [hp])
      rw [DTree.word_wrap, List.map_cons, List.map_append, List.map_cons, hb]
      exact Dyck.wrap a.1 (A.word.map Prod.fst) (B.word.map Prod.fst)
        (ihA hA) (ihB hB)

/-! ## 5.  A block cancels against itself exactly when it is not reduced -/

/-- **The characterisation.**  A matched pair with both ends in one block
exhibits a nonempty subword of that block's word which spells the identity.

The pair brackets a subtree; the subtree's word dies because the matching is
non-crossing, and the two ends of the pair are mutually inverse, so the whole
bracket dies.  Both ends carry the block's tag and blocks are contiguous, so the
bracket lies inside the block — and that is where the two end-only strip lemmas
of §1 are spent, since the interior of the bracket carries no tag constraint. -/
theorem exists_infix_mk_eq_one_of_selfPair [DecidableEq α]
    {T : DTree ((α × Bool) × Block)}
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1)
    {b : Block} {s : List (α × Bool)} (hblock : BlockAt T.word b s)
    {p : ((α × Bool) × Block) × ((α × Bool) × Block)} (hp : p ∈ T.pairs)
    (h1 : (p.1).2 = b) (h2 : (p.2).2 = b) :
    ∃ v : List (α × Bool), v ≠ [] ∧ v <:+: s ∧ FreeGroup.mk v = 1 := by
  obtain ⟨A₀, C₀, hL, hA, hC⟩ := hblock
  obtain ⟨X, Z, A, hw, hsub⟩ := DTree.exists_bracket_of_mem_pairs hp
  have hFL : (p.1 :: (A.word ++ [p.2])) <:+: A₀ ++ (tag b s ++ C₀) := by
    refine ⟨X, Z, ?_⟩
    rw [← hL, hw]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have hstep1 : (p.1 :: (A.word ++ [p.2])) <:+: tag b s ++ C₀ :=
    infix_of_infix_append_left hFL (fun hm => hA _ hm h1)
  have hrev : (p.1 :: (A.word ++ [p.2])).reverse
      = p.2 :: (A.word.reverse ++ [p.1]) := by simp
  have hstep2 : (p.1 :: (A.word ++ [p.2])) <:+: tag b s :=
    infix_of_infix_append_right hstep1 hrev (fun hm => hC _ hm h2)
  have hinf : (p.1 :: (A.word ++ [p.2])).map Prod.fst <:+: s := by
    have h3 := map_fst_infix hstep2
    rwa [map_fst_tag] at h3
  have hDA : Dyck (A.word.map (Prod.fst : (α × Bool) × Block → α × Bool)) :=
    dyck_word_map_fst A (fun q hq => hmatch q (hsub q hq))
  have hone : FreeGroup.mk ((p.1 :: (A.word ++ [p.2])).map Prod.fst) = 1 := by
    have hp2 : (p.2).1 = invLetter (p.1).1 := hmatch p hp
    rw [List.map_cons, List.map_append, List.map_cons, List.map_nil, hp2]
    exact mk_eq_one_of_dyck
      (Dyck.wrap (p.1).1 (A.word.map Prod.fst) [] hDA Dyck.nil)
  exact ⟨(p.1 :: (A.word ++ [p.2])).map Prod.fst, by simp, hinf, hone⟩

/-- **A reduced block has no self-pairing.**  The relators of a small-
cancellation family are reduced, so no relator block of the matching cancels
against its own letters.

Minimality of the expression is not used: reducedness alone refutes the
configuration, one block at a time. -/
theorem not_selfPair_of_blockAt [DecidableEq α]
    {T : DTree ((α × Bool) × Block)}
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1)
    {b : Block} {s : List (α × Bool)} (hblock : BlockAt T.word b s)
    (hred : FreeGroup.IsReduced s)
    {p : ((α × Bool) × Block) × ((α × Bool) × Block)} (hp : p ∈ T.pairs)
    (h1 : (p.1).2 = b) (h2 : (p.2).2 = b) : False := by
  obtain ⟨v, hvne, hvinf, hvone⟩ :=
    exists_infix_mk_eq_one_of_selfPair hmatch hblock hp h1 h2
  exact hvne (eq_nil_of_isReduced_of_mk_eq_one
    (isReduced_of_infix hvinf hred) hvone)

/-- **No relator cancels against itself**, on the matching of an actual labelled
expression, with the block located by `blockAt_relator_labelledWord`. -/
theorem not_selfPair_relator [DecidableEq α]
    {e e₁ e₂ : List (FreeGroup α × List (α × Bool))} {x : FreeGroup α}
    {s w : List (α × Bool)} {T : DTree ((α × Bool) × Block)}
    (hsplit : e = e₁ ++ (x, s) :: e₂)
    (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1)
    (hred : FreeGroup.IsReduced s)
    {p : ((α × Bool) × Block) × ((α × Bool) × Block)} (hp : p ∈ T.pairs)
    (h1 : (p.1).2 = Block.relator e₁.length)
    (h2 : (p.2).2 = Block.relator e₁.length) : False := by
  refine not_selfPair_of_blockAt hmatch ?_ hred hp h1 h2
  rw [hT]
  exact blockAt_relator_of_split hsplit

/-! ## 6.  A subword of a symmetrized relator, twice, is a piece -/

/-- **An occurrence anywhere is an occurrence at the front of a rotation.**  This
is why the classical definition of a piece may speak only of prefixes:
`symmetrization` is rotation-closed. -/
theorem exists_rotate_prefix_of_infix {u s : List (α × Bool)} (h : u <:+: s) :
    ∃ j : ℕ, u <+: s.rotate j := by
  obtain ⟨A, B, hAB⟩ := h
  exact ⟨A.length, prefix_rotate_of_append_prefix ⟨B, hAB⟩⟩

/-- `IsPiece` from two located occurrences. -/
theorem isPiece_of_prefix_rotate_two {R : Set (List (α × Bool))}
    {p s₁ s₂ : List (α × Bool)} {j₁ j₂ : ℕ}
    (h₁ : s₁ ∈ symmetrization R) (h₂ : s₂ ∈ symmetrization R)
    (hp₁ : p <+: s₁.rotate j₁) (hp₂ : p <+: s₂.rotate j₂)
    (hne : s₁.rotate j₁ ≠ s₂.rotate j₂) : IsPiece (symmetrization R) p :=
  isPiece_of_prefix_two (rotate_mem_symmetrization h₁ j₁)
    (rotate_mem_symmetrization h₂ j₂) hne hp₁ hp₂

/-- **The orientation, handled once.**  A run reads one word `u` forwards in one
relator and backwards-inverted in the other; `invRev u` is therefore a subword of
`invRev s₁` and of `s₂`, both symmetrized, and rotating each to bring it to the
front exhibits it as a piece.

The distinctness hypothesis is the one
`GreendlingerOverlap.isPiece_of_overlap` carries, quantified over the rotations
the location produces: the two relators are not one cyclic word read in opposite
directions. -/
theorem isPiece_of_run_infix {R : Set (List (α × Bool))}
    {u s₁ s₂ : List (α × Bool)}
    (h₁ : s₁ ∈ symmetrization R) (h₂ : s₂ ∈ symmetrization R)
    (hu₁ : u <:+: s₁) (hu₂ : FreeGroup.invRev u <:+: s₂)
    (hne : ∀ i j : ℕ, (FreeGroup.invRev s₁).rotate i ≠ s₂.rotate j) :
    IsPiece (symmetrization R) (FreeGroup.invRev u) := by
  obtain ⟨i, hi⟩ := exists_rotate_prefix_of_infix (invRev_infix_of_infix hu₁)
  obtain ⟨j, hj⟩ := exists_rotate_prefix_of_infix hu₂
  exact isPiece_of_prefix_rotate_two (invRev_mem_symmetrization h₁) h₂ hi hj
    (hne i j)

/-- **`C'(1/6)` read off a run.**  Six times the run is shorter than the relator
it lands in. -/
theorem six_mul_length_lt_of_run_infix {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {u s₁ s₂ : List (α × Bool)}
    (h₁ : s₁ ∈ symmetrization R) (h₂ : s₂ ∈ symmetrization R)
    (hu₁ : u <:+: s₁) (hu₂ : FreeGroup.invRev u <:+: s₂)
    (hne : ∀ i j : ℕ, (FreeGroup.invRev s₁).rotate i ≠ s₂.rotate j) :
    6 * u.length < s₂.length := by
  obtain ⟨j, hj⟩ := exists_rotate_prefix_of_infix hu₂
  have hpiece := isPiece_of_run_infix h₁ h₂ hu₁ hu₂ hne
  have h6 := six_mul_length_lt_of_isPiece hmetric hpiece
    (rotate_mem_symmetrization h₂ j) hj
  rwa [FreeGroup.invRev_length, List.length_rotate] at h6

/-! ## 7.  A run reads one subword in two blocks -/

/-- The closing letters of a run, read backwards and stripped of their labels,
invert its opening letters.  `MatchingSpine.reverse_map_snd_spineTail` on the
labelled word. -/
theorem map_fst_reverse_map_snd_spineTail [DecidableEq α]
    {T : DTree ((α × Bool) × Block)}
    (h : ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1) :
    ((T.spineTail.map Prod.snd).reverse).map
        (Prod.fst : (α × Bool) × Block → α × Bool)
      = FreeGroup.invRev ((T.spineTail.map Prod.fst).map Prod.fst) := by
  have hmap : (T.spineTail.map Prod.snd).map
      (Prod.fst : (α × Bool) × Block → α × Bool)
      = ((T.spineTail.map Prod.fst).map
          (Prod.fst : (α × Bool) × Block → α × Bool)).map invLetter := by
    simp only [List.map_map]
    refine List.map_congr_left ?_
    intro q hq
    exact h q (DTree.mem_pairs_of_mem_spineTail hq)
  rw [List.map_reverse, hmap]
  rfl

/-- **A run between two blocks reads one word twice.**  Its opening letters lie
in the first block and spell `u`; its closing letters lie in the second and spell
`invRev u`.  The run reads as many letters as it has pairs.

`MatchingSpine.word_eq_spineTail_core` puts the opening letters at the front of
the word the run heads and the closing letters at its back;
`BlockInfix.map_fst_infix_of_label`, through `infix_tag_of_forall`, puts each of
those inside its block. -/
theorem run_infix_of_blockAt [DecidableEq α]
    {T : DTree ((α × Bool) × Block)}
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1)
    {bk bl : Block} {sk sl : List (α × Bool)}
    (hk : BlockAt T.word bk sk) (hl : BlockAt T.word bl sl)
    (h1 : ∀ q ∈ T.spineTail, (q.1).2 = bk)
    (h2 : ∀ q ∈ T.spineTail, (q.2).2 = bl) :
    ∃ u : List (α × Bool), u.length = T.spineTail.length ∧
      u <:+: sk ∧ FreeGroup.invRev u <:+: sl := by
  obtain ⟨core, hcore⟩ := T.word_eq_spineTail_core
  refine ⟨(T.spineTail.map Prod.fst).map Prod.fst, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_map]
  · refine infix_tag_of_forall hk
      ⟨[], core ++ (T.spineTail.map Prod.snd).reverse, ?_⟩ ?_
    · rw [List.nil_append]
      exact hcore.symm
    · intro z hz
      rw [List.mem_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      exact h1 q hq
  · rw [← map_fst_reverse_map_snd_spineTail hmatch]
    refine infix_tag_of_forall hl
      ⟨(T.spineTail.map Prod.fst) ++ core, [], ?_⟩ ?_
    · rw [List.append_nil, List.append_assoc]
      exact hcore.symm
    · intro z hz
      rw [List.mem_reverse, List.mem_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      exact h2 q hq

/-! ## 8.  The interior price, in the shape the count wants -/

/-- **A run between two relators is bounded by `C'(1/6)`.**  Six times the number
of pairs in the run is less than the length of the relator its closing letters
lie in.

This is the interior-edge price the curvature count pays: a run is one edge of
the diagram, and this says how short an edge is compared with the faces it
separates. -/
theorem six_mul_length_lt_of_relator_run [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {T : DTree ((α × Bool) × Block)}
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1)
    {bk bl : Block} {sk sl : List (α × Bool)}
    (hk : BlockAt T.word bk sk) (hl : BlockAt T.word bl sl)
    (hsk : sk ∈ symmetrization R) (hsl : sl ∈ symmetrization R)
    (h1 : ∀ q ∈ T.spineTail, (q.1).2 = bk)
    (h2 : ∀ q ∈ T.spineTail, (q.2).2 = bl)
    (hne : ∀ i j : ℕ, (FreeGroup.invRev sk).rotate i ≠ sl.rotate j) :
    6 * T.spineTail.length < sl.length := by
  obtain ⟨u, hulen, hu1, hu2⟩ := run_infix_of_blockAt hmatch hk hl h1 h2
  have h6 := six_mul_length_lt_of_run_infix hmetric hsk hsl hu1 hu2 hne
  omega

/-- The piece itself, for a run between two relator blocks. -/
theorem isPiece_of_relator_run [DecidableEq α]
    {R : Set (List (α × Bool))}
    {T : DTree ((α × Bool) × Block)}
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1)
    {bk bl : Block} {sk sl : List (α × Bool)}
    (hk : BlockAt T.word bk sk) (hl : BlockAt T.word bl sl)
    (hsk : sk ∈ symmetrization R) (hsl : sl ∈ symmetrization R)
    (h1 : ∀ q ∈ T.spineTail, (q.1).2 = bk)
    (h2 : ∀ q ∈ T.spineTail, (q.2).2 = bl)
    (hne : ∀ i j : ℕ, (FreeGroup.invRev sk).rotate i ≠ sl.rotate j) :
    ∃ u : List (α × Bool), u.length = T.spineTail.length ∧
      IsPiece (symmetrization R) (FreeGroup.invRev u) := by
  obtain ⟨u, hulen, hu1, hu2⟩ := run_infix_of_blockAt hmatch hk hl h1 h2
  exact ⟨u, hulen, isPiece_of_run_infix hsk hsl hu1 hu2 hne⟩

end SmallCancellationRouter
end GroupApproximation
