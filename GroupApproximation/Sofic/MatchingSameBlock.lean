import GroupApproximation.Sofic.MatchingBoundaryBlock

/-!
# No block cancels against itself

`MatchingBoundaryBlock` proves that no matched pair joins two `Block.boundary`
letters, from the fact that the boundary block is a reduced suffix.  The
curvature count needs the same statement for **every** block, `relator k`
included, and this file supplies it.

## What has to be true of the blocks

The tree knows the matching and nothing else.  Two facts about how
`labelledWord` is *assembled* are what turn "which two blocks does this pair
join" into information:

* `Grouped` --- each block occupies a contiguous stretch.  Nothing carrying a
  different label ever sits between two occurrences of the same label, so a pair
  whose two ends carry the same label brackets a stretch that carries it too.
  `grouped_map_snd_labelledWord` proves it: `labelledWord` is a concatenation of
  tagged segments, one per block, and the tags are pairwise distinct.
* `BlocksReduced` --- each block is spelled by a reduced word.
  `blocksReduced_labelledWord` proves it from "the relators are reduced" and
  "`w` is reduced"; the conjugators need no hypothesis, because
  `FreeGroup.toWord` is reduced by construction.

## The theorem

`blk_ne_of_mem_pairs`: over a matched tree whose labels are grouped and whose
blocks are reduced, **no matched pair has both of its ends in the same block**.

The proof is a structural induction.  At a node `wrap a b A B`, if `a` and `b`
carried the same label then, labels being contiguous, everything in `A.word`
would carry it too --- so `a :: (A.word ++ [b])` is a constant-block stretch,
hence reduced, and `DTree.not_wrap_of_isReduced` refutes the node outright.

`block_ne_of_mem_pairs_labelledWord` is the reading on the expression's own
diagram, with both hypotheses discharged.  In diagram language: **no region of
the picture cancels against itself.**

## Relation to the boundary case

This is strictly stronger than `MatchingBoundaryBlock.not_boundary_pair` in what
it concludes, and strictly weaker in what it costs: it reads reducedness of
*every* block, so it needs the relators reduced, while the boundary case needs
only `w`.  Neither supersedes the other, and the two are proved by different
routes --- the boundary case by locating the block as a suffix, this one by the
interval structure of all the blocks at once.

## Why the count needs it

The degree bound the count is after --- some `relator k` block meets at most
three others in maximal runs --- reduces, for a *simple* block graph, to the
outerplanar edge bound `E < 2V`.  Simplicity is what this theorem buys: two
relator blocks cannot be joined by two different maximal runs, because between
two such runs every letter would have to be matched inside one block.

Nothing here proves the degree bound, the edge bound, or run uniqueness.

Unconditional: no small cancellation, no minimality, no metric condition.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u v

variable {α : Type*}

/-! ## 1.  Equal labels are contiguous -/

/-- **Blocks are intervals.**  Nothing carrying a different label ever sits
between two occurrences of the same label.

`DTree` does not carry this --- the tree knows the matching, not the blocks.  It
is a fact about the *construction* of `labelledWord`, which concatenates one
tagged segment per block. -/
def Grouped {γ : Type*} (l : List γ) : Prop :=
  ∀ (p m s : List γ) (b : γ), l = p ++ b :: (m ++ b :: s) → ∀ c ∈ m, c = b

theorem grouped_nil {γ : Type*} : Grouped ([] : List γ) := by
  intro p m s b hEq c hc
  exfalso
  have h := congrArg List.length hEq
  simp only [List.length_nil, List.length_append, List.length_cons] at h
  omega

/-- Being grouped passes to contiguous subwords. -/
theorem Grouped.infix {γ : Type*} {l l' : List γ} (h : Grouped l)
    (hi : l' <:+: l) : Grouped l' := by
  obtain ⟨X, Y, hXY⟩ := hi
  intro p m s b hl' c hc
  refine h (X ++ p) m (s ++ Y) b ?_ c hc
  rw [← hXY, hl']
  simp only [List.append_assoc, List.cons_append]

/-- A constant run is grouped. -/
theorem grouped_replicate {γ : Type*} (n : ℕ) (b : γ) :
    Grouped (List.replicate n b) := by
  intro p m s b' hEq c hc
  have hb' : b' = b := by
    refine List.eq_of_mem_replicate (n := n) ?_
    rw [hEq]
    exact List.mem_append_right _ List.mem_cons_self
  have hcb : c = b := by
    refine List.eq_of_mem_replicate (n := n) ?_
    rw [hEq]
    exact List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_append_left _ hc))
  rw [hcb, hb']

/-- **Concatenating with disjoint label sets preserves grouping.**  The two
occurrences of a repeated label lie on the same side, because no label occurs on
both, and then that side's grouping decides the stretch between them. -/
theorem grouped_append {γ : Type*} {l₁ l₂ : List γ} (h₁ : Grouped l₁)
    (h₂ : Grouped l₂) (hdisj : ∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) :
    Grouped (l₁ ++ l₂) := by
  intro p m s b hEq c hc
  have hEq' : p ++ (b :: (m ++ b :: s)) = l₁ ++ l₂ := hEq.symm
  rcases List.append_eq_append_iff.mp hEq' with ⟨Z, hl₁, hR⟩ | ⟨Z, -, hl₂⟩
  · rcases Z with _ | ⟨z, Z'⟩
    · rw [List.nil_append] at hR
      exact h₂ [] m s b (by rw [List.nil_append]; exact hR.symm) c hc
    · rw [List.cons_append] at hR
      simp only [List.cons.injEq] at hR
      obtain ⟨hzb, hR'⟩ := hR
      have hbl₁ : b ∈ l₁ := by
        rw [hl₁, ← hzb]
        exact List.mem_append_right _ List.mem_cons_self
      rcases List.append_eq_append_iff.mp hR' with ⟨W, hZ', hbs⟩ | ⟨W, -, hl₂'⟩
      · rcases W with _ | ⟨w', W'⟩
        · rw [List.nil_append] at hbs
          exfalso
          refine hdisj b hbl₁ b ?_ rfl
          rw [← hbs]
          exact List.mem_cons_self
        · rw [List.cons_append] at hbs
          simp only [List.cons.injEq] at hbs
          obtain ⟨hbw, -⟩ := hbs
          refine h₁ p m W' b ?_ c hc
          rw [hl₁, ← hzb, hZ', ← hbw]
      · exfalso
        refine hdisj b hbl₁ b ?_ rfl
        rw [hl₂']
        exact List.mem_append_right _ List.mem_cons_self
  · exact h₂ Z m s b hl₂ c hc

/-! ## 2.  A matched pair never has both ends in one block -/

/-- **No block cancels against itself.**

If a matched pair carried the same label at both ends then, labels being
contiguous, everything the pair brackets would carry that label too --- so the
opening letter, the bracketed word and the closing letter form a stretch of a
*single* block, which is reduced, and `DTree.not_wrap_of_isReduced` says no pair
encloses a reduced stretch.

This is the combinatorial form of "a region of the diagram does not cancel
against itself", and it is the first place the count needs something `DTree`
does not carry: the interval structure of the blocks. -/
theorem blk_ne_of_mem_pairs [DecidableEq α] {β : Type u} {γ : Type v}
    {ℓ : β → α × Bool} {blk : β → γ} :
    ∀ T : DTree β, (∀ p ∈ T.pairs, ℓ p.2 = invLetter (ℓ p.1)) →
      Grouped (T.word.map blk) →
      (∀ M : List β, M <:+: T.word →
        (∀ x ∈ M, ∀ y ∈ M, blk x = blk y) → FreeGroup.IsReduced (M.map ℓ)) →
      ∀ p ∈ T.pairs, blk p.1 ≠ blk p.2 := by
  intro T
  induction T with
  | nil =>
      intro _hmatch _hgroup _hred p hp
      exact absurd hp (by simp)
  | wrap a b A B ihA ihB =>
      intro hmatch hgroup hred p hp
      have hAinf : A.word <:+: (DTree.wrap a b A B).word :=
        ⟨[a], b :: B.word, by simp⟩
      have hBinf : B.word <:+: (DTree.wrap a b A B).word :=
        ⟨a :: (A.word ++ [b]), [], by simp⟩
      have hmatchA : ∀ q ∈ A.pairs, ℓ q.2 = invLetter (ℓ q.1) := fun q hq =>
        hmatch q (by simp [hq])
      have hmatchB : ∀ q ∈ B.pairs, ℓ q.2 = invLetter (ℓ q.1) := fun q hq =>
        hmatch q (by simp [hq])
      rw [DTree.pairs_wrap, List.mem_cons] at hp
      rcases hp with rfl | hp
      · show blk a ≠ blk b
        intro heq
        have hall : ∀ c ∈ A.word.map blk, c = blk a := by
          refine hgroup [] (A.word.map blk) (B.word.map blk) (blk a) ?_
          simp only [DTree.word_wrap, List.map_cons, List.map_append,
            List.nil_append]
          rw [← heq]
        have hconst : ∀ x ∈ a :: (A.word ++ [b]), blk x = blk a := by
          intro x hx
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · rfl
          · rcases List.mem_append.mp hx with hx' | hx'
            · exact hall (blk x) (List.mem_map_of_mem hx')
            · rw [List.mem_singleton.mp hx', ← heq]
        have hMinf : (a :: (A.word ++ [b])) <:+: (DTree.wrap a b A B).word :=
          ⟨[], B.word, by simp⟩
        have hMred : FreeGroup.IsReduced ((a :: (A.word ++ [b])).map ℓ) := by
          refine hred _ hMinf ?_
          intro x hx y hy
          rw [hconst x hx, hconst y hy]
        exact DTree.not_wrap_of_isReduced hmatch hMred
      · rcases List.mem_append.mp hp with hp' | hp'
        · exact ihA hmatchA (hgroup.infix (infix_map_of_infix blk hAinf))
            (fun M hM hcst => hred M (hM.trans hAinf) hcst) p hp'
        · exact ihB hmatchB (hgroup.infix (infix_map_of_infix blk hBinf))
            (fun M hM hcst => hred M (hM.trans hBinf) hcst) p hp'

/-! ## 3.  The labelled word is grouped -/

/-- The index of the factor a block belongs to.  `boundary` belongs to no
factor and is given `0`; it never occurs in a `labelledExpr`
(`snd_ne_boundary_of_mem_labelledExpr`), so the value is never read. -/
def Block.index : Block → ℕ
  | Block.conj k => k
  | Block.relator k => k
  | Block.stem k => k
  | Block.boundary => 0

/-- A tagged segment is a constant run of labels. -/
theorem map_snd_tag (b : Block) (l : List (α × Bool)) :
    (tag b l).map Prod.snd = List.replicate l.length b := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [List.length_cons, List.replicate_succ, ← ih]
      rfl

/-- One labelled factor is three constant runs. -/
theorem map_snd_labelledFactor (k : ℕ) (c s : List (α × Bool)) :
    (labelledFactor k c s).map Prod.snd
      = List.replicate c.length (Block.conj k)
        ++ (List.replicate s.length (Block.relator k)
          ++ List.replicate c.length (Block.stem k)) := by
  rw [labelledFactor, List.map_append, List.map_append, map_snd_tag,
    map_snd_tag, map_snd_tag, FreeGroup.invRev_length]

/-- The labels of a factor are that factor's three. -/
theorem mem_map_snd_labelledFactor {k : ℕ} {c s : List (α × Bool)} {b : Block}
    (h : b ∈ (labelledFactor k c s).map Prod.snd) :
    b = Block.conj k ∨ b = Block.relator k ∨ b = Block.stem k := by
  rw [map_snd_labelledFactor, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl (List.eq_of_mem_replicate h)
  · rcases List.mem_append.mp h with h | h
    · exact Or.inr (Or.inl (List.eq_of_mem_replicate h))
    · exact Or.inr (Or.inr (List.eq_of_mem_replicate h))

/-- The labels of one factor all carry that factor's index. -/
theorem index_eq_of_mem_labelledFactor {k : ℕ} {c s : List (α × Bool)}
    {b : Block} (h : b ∈ (labelledFactor k c s).map Prod.snd) : b.index = k := by
  rcases mem_map_snd_labelledFactor h with h' | h' | h' <;> rw [h'] <;> rfl

/-- One labelled factor is grouped: three constant runs with distinct labels. -/
theorem grouped_map_snd_labelledFactor (k : ℕ) (c s : List (α × Bool)) :
    Grouped ((labelledFactor k c s).map Prod.snd) := by
  rw [map_snd_labelledFactor]
  refine grouped_append (grouped_replicate _ _)
    (grouped_append (grouped_replicate _ _) (grouped_replicate _ _) ?_) ?_
  · intro x hx y hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
    exact fun hh => Block.noConfusion hh
  · intro x hx y hy
    rw [List.eq_of_mem_replicate hx]
    rcases List.mem_append.mp hy with h | h
    · rw [List.eq_of_mem_replicate h]
      exact fun hh => Block.noConfusion hh
    · rw [List.eq_of_mem_replicate h]
      exact fun hh => Block.noConfusion hh

/-- Every label of a labelled expression belongs to a factor of index at least
the starting one, and is not the boundary. -/
theorem mem_map_snd_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))) (b : Block),
      b ∈ (labelledExpr k e).map Prod.snd →
        k ≤ b.index ∧ b ≠ Block.boundary := by
  intro k e
  induction e generalizing k with
  | nil =>
      intro b hb
      rw [labelledExpr_nil, List.map_nil] at hb
      exact absurd hb (by simp)
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      intro b hb
      rw [labelledExpr_cons, List.map_append, List.mem_append] at hb
      rcases hb with h | h
      · refine ⟨le_of_eq (index_eq_of_mem_labelledFactor h).symm, ?_⟩
        rcases mem_map_snd_labelledFactor h with h' | h' | h' <;> rw [h'] <;>
          exact fun hh => Block.noConfusion hh
      · obtain ⟨h1, h2⟩ := ih (k + 1) b h
        exact ⟨by omega, h2⟩

/-- A labelled expression is grouped: one factor's three runs, then the rest,
and the factor indices separate them. -/
theorem grouped_map_snd_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      Grouped ((labelledExpr k e).map Prod.snd) := by
  intro k e
  induction e generalizing k with
  | nil =>
      rw [labelledExpr_nil, List.map_nil]
      exact grouped_nil
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      rw [labelledExpr_cons, List.map_append]
      refine grouped_append (grouped_map_snd_labelledFactor _ _ _)
        (ih (k + 1)) ?_
      intro y hy z hz
      have hy' : y.index = k := index_eq_of_mem_labelledFactor hy
      obtain ⟨hz', -⟩ := mem_map_snd_labelledExpr (k + 1) e z hz
      intro hEq
      rw [hEq] at hy'
      omega

/-- **The labelled word is grouped.**  The expression part is grouped, the
boundary part is a constant run, and no label occurs in both.

This is one of the two hypotheses `blk_ne_of_mem_pairs` reads, discharged for
the object the count runs on. -/
theorem grouped_map_snd_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    Grouped ((labelledWord e w).map Prod.snd) := by
  rw [labelledWord, List.map_append, map_snd_tag]
  refine grouped_append (grouped_map_snd_labelledExpr 0 e)
    (grouped_replicate _ _) ?_
  intro x hx y hy
  obtain ⟨-, h2⟩ := mem_map_snd_labelledExpr 0 e x hx
  rw [List.eq_of_mem_replicate hy]
  exact h2

/-! ## 4.  Each block is spelled by a reduced word -/

/-- The mirror of `exists_split_of_infix`: with the `P`-letters confined to the
*prefix*, a contiguous subword is a piece of that prefix followed by a `P`-free
stretch. -/
theorem exists_split_of_infix' {β : Type u} {P : β → Prop} {X Y M : List β}
    (hM : M <:+: X ++ Y) (hY : ∀ z ∈ Y, ¬ P z) :
    ∃ X' Y', M = X' ++ Y' ∧ X' <:+: X ∧ (∀ z ∈ Y', ¬ P z) := by
  obtain ⟨p, q, hpq⟩ := hM
  have hEq : p ++ (M ++ q) = X ++ Y := by
    rw [← hpq, List.append_assoc]
  rcases List.append_eq_append_iff.mp hEq with ⟨Z, hXZ, hMq⟩ | ⟨Z, -, hYZ⟩
  · rcases List.append_eq_append_iff.mp hMq with ⟨W, hZW, -⟩ | ⟨W, hMZW, hYW⟩
    · refine ⟨M, [], (List.append_nil M).symm, ⟨p, W, ?_⟩, by simp⟩
      rw [hXZ, hZW, List.append_assoc]
    · refine ⟨Z, W, hMZW, ⟨p, [], by rw [List.append_nil, hXZ]⟩, ?_⟩
      intro z hz
      refine hY z ?_
      rw [hYW]
      exact List.mem_append_left _ hz
  · refine ⟨[], M, rfl, ⟨[], X, by simp⟩, ?_⟩
    intro z hz
    refine hY z ?_
    rw [hYZ]
    exact List.mem_append_right _ (List.mem_append_left _ hz)

/-- A `P`-constant subword of `l₁ ++ l₂` with no `P`-letter in `l₁` lies in
`l₂`. -/
theorem infix_right_of_infix_append {β : Type u} {P : β → Prop}
    {l₁ l₂ M : List β} (hM : M <:+: l₁ ++ l₂) (hMP : ∀ z ∈ M, P z)
    (h₁ : ∀ z ∈ l₁, ¬ P z) : M <:+: l₂ := by
  obtain ⟨X', Y', hMeq, hX', hY'⟩ := exists_split_of_infix hM h₁
  have hX'nil : X' = [] := by
    rcases X' with _ | ⟨x, X''⟩
    · rfl
    · refine absurd (hMP x ?_) (hX' x List.mem_cons_self)
      rw [hMeq]
      exact List.mem_append_left _ List.mem_cons_self
  rw [hMeq, hX'nil, List.nil_append]
  exact hY'

/-- A `P`-constant subword of `l₁ ++ l₂` with no `P`-letter in `l₂` lies in
`l₁`. -/
theorem infix_left_of_infix_append {β : Type u} {P : β → Prop}
    {l₁ l₂ M : List β} (hM : M <:+: l₁ ++ l₂) (hMP : ∀ z ∈ M, P z)
    (h₂ : ∀ z ∈ l₂, ¬ P z) : M <:+: l₁ := by
  obtain ⟨X', Y', hMeq, hX', hY'⟩ := exists_split_of_infix' hM h₂
  have hY'nil : Y' = [] := by
    rcases Y' with _ | ⟨y, Y''⟩
    · rfl
    · refine absurd (hMP y ?_) (hY' y List.mem_cons_self)
      rw [hMeq]
      exact List.mem_append_right _ List.mem_cons_self
  rw [hMeq, hY'nil, List.append_nil]
  exact hX'

/-- **Every constant-block subword maps to a reduced word.**  The second thing
`blk_ne_of_mem_pairs` reads, and again a fact about the construction rather than
about the tree: each block is one tagged segment, tagged from a reduced word. -/
def BlocksReduced (l : List ((α × Bool) × Block)) : Prop :=
  ∀ M : List ((α × Bool) × Block), M <:+: l →
    (∀ x ∈ M, ∀ y ∈ M, x.2 = y.2) → FreeGroup.IsReduced (M.map Prod.fst)

/-- A tagged segment of a reduced word has reduced blocks. -/
theorem blocksReduced_tag (b : Block) {l : List (α × Bool)}
    (h : FreeGroup.IsReduced l) : BlocksReduced (tag b l) := by
  intro M hM _
  refine isReduced_of_infix ?_ h
  rw [← map_fst_tag b l]
  exact infix_map_of_infix Prod.fst hM

/-- Concatenating with disjoint label sets preserves it: a constant-block
subword of the join cannot meet both sides. -/
theorem blocksReduced_append {l₁ l₂ : List ((α × Bool) × Block)}
    (h₁ : BlocksReduced l₁) (h₂ : BlocksReduced l₂)
    (hdisj : ∀ x ∈ l₁, ∀ y ∈ l₂, x.2 ≠ y.2) : BlocksReduced (l₁ ++ l₂) := by
  intro M hM hconst
  rcases M with _ | ⟨z, M'⟩
  · rw [List.map_nil]
    exact FreeGroup.IsReduced.nil
  · have hMP : ∀ u ∈ z :: M', u.2 = z.2 := fun u hu =>
      hconst u hu z List.mem_cons_self
    by_cases hb : ∃ y ∈ l₁, y.2 = z.2
    · obtain ⟨y, hy, hyz⟩ := hb
      have h₂' : ∀ u ∈ l₂, ¬ (u.2 = z.2) := by
        intro u hu huz
        exact hdisj y hy u hu (by rw [hyz, huz])
      exact h₁ _ (infix_left_of_infix_append hM hMP h₂') hconst
    · have h₁' : ∀ u ∈ l₁, ¬ (u.2 = z.2) := by
        intro u hu huz
        exact hb ⟨u, hu, huz⟩
      exact h₂ _ (infix_right_of_infix_append hM hMP h₁') hconst

/-- One labelled factor has reduced blocks. -/
theorem blocksReduced_labelledFactor (k : ℕ) {c s : List (α × Bool)}
    (hc : FreeGroup.IsReduced c) (hs : FreeGroup.IsReduced s) :
    BlocksReduced (labelledFactor k c s) := by
  rw [labelledFactor]
  refine blocksReduced_append (blocksReduced_tag _ hc)
    (blocksReduced_append (blocksReduced_tag _ hs)
      (blocksReduced_tag _ (isReduced_invRev_iff.mpr hc)) ?_) ?_
  · intro x hx y hy
    rw [snd_eq_of_mem_tag hx, snd_eq_of_mem_tag hy]
    exact fun hh => Block.noConfusion hh
  · intro x hx y hy
    rw [snd_eq_of_mem_tag hx]
    rcases List.mem_append.mp hy with h | h
    · rw [snd_eq_of_mem_tag h]
      exact fun hh => Block.noConfusion hh
    · rw [snd_eq_of_mem_tag h]
      exact fun hh => Block.noConfusion hh

/-- A labelled expression has reduced blocks, given reduced relators.  The
conjugators need no hypothesis: `FreeGroup.toWord` is reduced by
construction. -/
theorem blocksReduced_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      (∀ q ∈ e, FreeGroup.IsReduced q.2) → BlocksReduced (labelledExpr k e) := by
  intro k e
  induction e generalizing k with
  | nil =>
      intro _
      rw [labelledExpr_nil]
      intro M hM _
      have hMnil : M = [] := by
        have hle := hM.length_le
        rw [List.length_nil] at hle
        exact List.length_eq_zero_iff.mp (by omega)
      rw [hMnil, List.map_nil]
      exact FreeGroup.IsReduced.nil
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      intro hs
      rw [labelledExpr_cons]
      refine blocksReduced_append
        (blocksReduced_labelledFactor k FreeGroup.isReduced_toWord
          (hs (x, s) List.mem_cons_self))
        (ih (k + 1) (fun q hq => hs q (List.mem_cons_of_mem _ hq))) ?_
      intro y hy z hz
      obtain ⟨h3, -⟩ :=
        mem_map_snd_labelledExpr (k + 1) e z.2 (List.mem_map_of_mem hz)
      have hidx : (y.2).index = k :=
        index_eq_of_mem_labelledFactor (List.mem_map_of_mem hy)
      intro hEq
      rw [hEq] at hidx
      omega

/-- **The labelled word has reduced blocks.**  Only the relators and the target
word need to be reduced; everything else is automatic. -/
theorem blocksReduced_labelledWord [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hs : ∀ q ∈ e, FreeGroup.IsReduced q.2) (hw : FreeGroup.IsReduced w) :
    BlocksReduced (labelledWord e w) := by
  rw [labelledWord]
  refine blocksReduced_append (blocksReduced_labelledExpr 0 e hs)
    (blocksReduced_tag _ (isReduced_invRev_iff.mpr hw)) ?_
  intro x hx y hy
  obtain ⟨-, h2⟩ :=
    mem_map_snd_labelledExpr 0 e x.2 (List.mem_map_of_mem hx)
  rw [snd_eq_of_mem_tag hy]
  exact h2

/-! ## 5.  Read on the expression's own diagram -/

/-- **No matched pair of the expression's diagram has both ends in one block.**

Both hypotheses of `blk_ne_of_mem_pairs` are discharged for the object the
curvature count runs on: the blocks of `labelledWord e w` are intervals
(`grouped_map_snd_labelledWord`) and each is spelled by a reduced word
(`blocksReduced_labelledWord`).  Nothing about small cancellation is read, and
no minimality --- only that the relators and the target word are reduced.

In diagram language: no region of the picture cancels against itself.  Two
consequences the curvature count needs follow from it, and neither is proved
here: a relator block meets another relator block in at most one maximal run,
and there is therefore no parallel edge in the block graph. -/
theorem block_ne_of_mem_pairs_labelledWord [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hs : ∀ q ∈ e, FreeGroup.IsReduced q.2) (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, (p.1).2 ≠ (p.2).2 := by
  refine blk_ne_of_mem_pairs (ℓ := Prod.fst) (blk := Prod.snd) T hmatch ?_ ?_
  · rw [hT]
    exact grouped_map_snd_labelledWord e w
  · rw [hT]
    exact blocksReduced_labelledWord hs hw

end SmallCancellationRouter
end GroupApproximation
