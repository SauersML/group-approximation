import GroupApproximation.Sofic.BlockInfix
import GroupApproximation.Sofic.MatchingSameBlock
import GroupApproximation.Sofic.MatchingChordGraph

/-!
# The blocks of the labelled word are in order, so the chord machinery applies

`MatchingChordGraph` proves that the matched pairs of a `DTree`, read through a
**monotone** labelling `pos : ℕ → ℕ` of positions by blocks, form a non-crossing
chord set — and it leaves monotonicity as a hypothesis.  Nothing discharged that
hypothesis, so the chord machinery was, strictly, about nothing.  This file
builds the labelling for `ConjExprMatching.labelledWord` and proves it monotone,
which is the whole of what "the blocks are intervals, in order" amounts to once
stated positionally.

## The labelling

    `blockPos n (conj k)    = 3k`
    `blockPos n (relator k) = 3k + 1`
    `blockPos n (stem k)    = 3k + 2`
    `blockPos n boundary    = 3n`

with `n` the number of factors.  Three values per factor in the order the factor
spells them, and the boundary above every factor because every factor index is
`< n` (`BlockInfix.index_mem_range_of_mem_labelledExpr`) — so a factor's value is
at most `3(n − 1) + 2 = 3n − 1`.

`wordPos e w` reads a position of `labelledWord e w` through it, and takes the
value `3n + 1` past the end of the word, which is above everything so that
monotonicity survives the overflow without a side condition.

## What is proved

* `pairwise_map_blockPos_labelledWord` — the blocks of the labelled word are
  weakly increasing.  Structural: each tagged segment is constant, a factor is
  three constant segments in increasing order, the expression is factors in
  increasing index order, and the boundary is above all of them.  `List.Pairwise`
  over `List.pairwise_append`, so the recursion never mentions an index.
* `wordPos_monotone` — the positional form, including past the end.
* `wordPos_eq_of_mem_pairIdx` — the bridge from *positions* to *values*: at the
  two ends of a matched pair, `wordPos` reads the blocks of that pair's two
  entries.  This is what lets `MatchingSameBlock`'s theorem about `T.pairs` be
  spent on a hypothesis about `T.pairIdx`.
* `wordPos_ne_of_mem_pairIdx` — consequently the two ends of a matched pair get
  **different** values, which is the second hypothesis `MatchingChordGraph` asks
  for.  `blockPos` is injective where it is read: the three values of a factor
  are distinct, factors have distinct indices, and the boundary is strictly above
  all of them.
* `exists_block_degree_le_four` — the degree bound with **no hypotheses left
  about the labelling**: for a reduced `w`, reduced relators, and a matching of
  `labelledWord e w`, some block other than the boundary is matched into at most
  four blocks.

That last statement is the point of the file.  What it does *not* say — see
`CurvatureStemThreshold` — is that the block it produces is a *relator* block:
with the conjugator blocks present as vertices the count does not close, and the
block handed back may be a `conj` or `stem` block.  The chord machinery is now
unconditional; the stem problem is untouched.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The labelling -/

/-- **The blocks in the order the word spells them.**  Three values per factor,
and the boundary above every factor. -/
def blockPos (n : ℕ) : Block → ℕ
  | Block.conj k => 3 * k
  | Block.relator k => 3 * k + 1
  | Block.stem k => 3 * k + 2
  | Block.boundary => 3 * n

@[simp] theorem blockPos_conj (n k : ℕ) : blockPos n (Block.conj k) = 3 * k := rfl

@[simp] theorem blockPos_relator (n k : ℕ) :
    blockPos n (Block.relator k) = 3 * k + 1 := rfl

@[simp] theorem blockPos_stem (n k : ℕ) :
    blockPos n (Block.stem k) = 3 * k + 2 := rfl

@[simp] theorem blockPos_boundary (n : ℕ) : blockPos n Block.boundary = 3 * n := rfl

/-- A factor's three blocks take the three values `3k`, `3k + 1`, `3k + 2`. -/
theorem blockPos_bounds {n k : ℕ} {b : Block}
    (h : b = Block.conj k ∨ b = Block.relator k ∨ b = Block.stem k) :
    3 * k ≤ blockPos n b ∧ blockPos n b ≤ 3 * k + 2 := by
  rcases h with rfl | rfl | rfl <;> simp

/-- **`blockPos` separates distinct blocks wherever it is read.**  The three
values of a factor are distinct, factors of different index are separated by
their index, and the boundary — sitting at `3n` — is above every factor, whose
index is `< n`. -/
theorem blockPos_injOn {n : ℕ} {b b' : Block}
    (hb : (∃ k < n, b = Block.conj k ∨ b = Block.relator k ∨ b = Block.stem k)
      ∨ b = Block.boundary)
    (hb' : (∃ k < n, b' = Block.conj k ∨ b' = Block.relator k ∨ b' = Block.stem k)
      ∨ b' = Block.boundary)
    (h : blockPos n b = blockPos n b') : b = b' := by
  rcases hb with ⟨k, hk, hbk⟩ | rfl
  · rcases hb' with ⟨k', hk', hbk'⟩ | rfl
    · rcases hbk with rfl | rfl | rfl <;> rcases hbk' with rfl | rfl | rfl <;>
        simp only [blockPos_conj, blockPos_relator, blockPos_stem] at h <;>
          [skip; omega; omega; omega; skip; omega; omega; omega; skip] <;>
          · have : k = k' := by omega
            rw [this]
    · rcases hbk with rfl | rfl | rfl <;>
        simp only [blockPos_conj, blockPos_relator, blockPos_stem,
          blockPos_boundary] at h <;> omega
  · rcases hb' with ⟨k', hk', hbk'⟩ | rfl
    · rcases hbk' with rfl | rfl | rfl <;>
        simp only [blockPos_conj, blockPos_relator, blockPos_stem,
          blockPos_boundary] at h <;> omega
    · rfl

/-! ## 2.  The word's blocks are weakly increasing -/

/-- A list whose entries all agree is weakly increasing. -/
theorem pairwise_le_of_const {l : List ℕ} {c : ℕ} (h : ∀ x ∈ l, x = c) :
    List.Pairwise (· ≤ ·) l := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
      refine List.Pairwise.cons ?_ (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
      intro b hb
      rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]

/-- Every value of a tagged segment is that tag's value. -/
theorem map_blockPos_tag_const (n : ℕ) (b : Block) (l : List (α × Bool)) :
    ∀ v ∈ (tag b l).map (fun z => blockPos n z.2), v = blockPos n b := by
  intro v hv
  obtain ⟨z, hz, hvz⟩ := List.mem_map.mp hv
  rw [← hvz, snd_eq_of_mem_tag hz]

/-- Every value of a labelled factor lies in that factor's window. -/
theorem map_blockPos_labelledFactor_bounds (n k : ℕ) (c s : List (α × Bool)) :
    ∀ v ∈ (labelledFactor k c s).map (fun z => blockPos n z.2),
      3 * k ≤ v ∧ v ≤ 3 * k + 2 := by
  intro v hv
  obtain ⟨z, hz, hvz⟩ := List.mem_map.mp hv
  rw [← hvz]
  exact blockPos_bounds (mem_map_snd_labelledFactor (List.mem_map_of_mem hz))

/-- **One factor is weakly increasing**: three constant runs at `3k`, `3k + 1`,
`3k + 2`, in that order. -/
theorem pairwise_map_blockPos_labelledFactor (n k : ℕ) (c s : List (α × Bool)) :
    List.Pairwise (· ≤ ·) ((labelledFactor k c s).map (fun z => blockPos n z.2)) := by
  rw [labelledFactor, List.map_append, List.map_append]
  refine List.pairwise_append.mpr ⟨pairwise_le_of_const
    (map_blockPos_tag_const n (Block.conj k) c), ?_, ?_⟩
  · refine List.pairwise_append.mpr ⟨pairwise_le_of_const
      (map_blockPos_tag_const n (Block.relator k) s), pairwise_le_of_const
      (map_blockPos_tag_const n (Block.stem k) (FreeGroup.invRev c)), ?_⟩
    intro a ha b hb
    rw [map_blockPos_tag_const n (Block.relator k) s a ha,
      map_blockPos_tag_const n (Block.stem k) (FreeGroup.invRev c) b hb]
    simp
  · intro a ha b hb
    rw [map_blockPos_tag_const n (Block.conj k) c a ha]
    rcases List.mem_append.mp hb with h | h
    · rw [map_blockPos_tag_const n (Block.relator k) s b h]
      simp
    · rw [map_blockPos_tag_const n (Block.stem k) (FreeGroup.invRev c) b h]
      simp

/-- Every value of a labelled expression lies at or above its starting factor,
and strictly below the window of the factor past its last. -/
theorem map_blockPos_labelledExpr_bounds [DecidableEq α] (n : ℕ) :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (v : ℕ), v ∈ (labelledExpr k e).map (fun z => blockPos n z.2) →
      3 * k ≤ v ∧ v < 3 * (k + e.length) := by
  intro k e v hv
  obtain ⟨z, hz, hvz⟩ := List.mem_map.mp hv
  obtain ⟨j, hjk, hjlt, hlab⟩ := index_mem_range_of_mem_labelledExpr k e z hz
  obtain ⟨h1, h2⟩ := blockPos_bounds (n := n) hlab
  rw [← hvz]
  omega

/-- **A labelled expression is weakly increasing**: one factor's three runs, then
the rest, and the factor indices separate them. -/
theorem pairwise_map_blockPos_labelledExpr [DecidableEq α] (n : ℕ) :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      List.Pairwise (· ≤ ·) ((labelledExpr k e).map (fun z => blockPos n z.2)) := by
  intro k e
  induction e generalizing k with
  | nil =>
      rw [labelledExpr_nil, List.map_nil]
      exact List.Pairwise.nil
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      rw [labelledExpr_cons, List.map_append]
      refine List.pairwise_append.mpr
        ⟨pairwise_map_blockPos_labelledFactor n k _ s, ih (k + 1), ?_⟩
      intro a ha b hb
      obtain ⟨-, h2⟩ := map_blockPos_labelledFactor_bounds n k x.toWord s a ha
      obtain ⟨h3, -⟩ := map_blockPos_labelledExpr_bounds n (k + 1) e b hb
      omega

/-- **The labelled word is weakly increasing.**  The expression part is, the
boundary part is constant at `3n`, and every factor value is at most `3n − 1`
because every factor index is `< n`. -/
theorem pairwise_map_blockPos_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    List.Pairwise (· ≤ ·)
      ((labelledWord e w).map (fun z => blockPos e.length z.2)) := by
  rw [labelledWord, List.map_append]
  refine List.pairwise_append.mpr ⟨pairwise_map_blockPos_labelledExpr _ 0 e,
    pairwise_le_of_const (map_blockPos_tag_const _ Block.boundary _), ?_⟩
  intro a ha b hb
  obtain ⟨-, h2⟩ := map_blockPos_labelledExpr_bounds e.length 0 e a ha
  rw [map_blockPos_tag_const _ Block.boundary _ b hb]
  simp only [blockPos_boundary]
  omega

/-- **Every value of the labelled word is at most `3n`.**  Needed so that the
overflow value `3n + 1` sits above the word. -/
theorem map_blockPos_labelledWord_le [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    ∀ v ∈ (labelledWord e w).map (fun z => blockPos e.length z.2),
      v ≤ 3 * e.length := by
  intro v hv
  rw [labelledWord, List.map_append, List.mem_append] at hv
  rcases hv with h | h
  · obtain ⟨-, h2⟩ := map_blockPos_labelledExpr_bounds e.length 0 e v h
    omega
  · rw [map_blockPos_tag_const _ Block.boundary _ v h]
    simp

/-! ## 3.  The positional labelling -/

/-- **The block at a position**, and a value above every block past the end of
the word.  The overflow value keeps monotonicity total, so no consumer carries a
range side condition. -/
def wordPos [DecidableEq α] (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) (x : ℕ) : ℕ :=
  match (labelledWord e w)[x]? with
  | some z => blockPos e.length z.2
  | none => 3 * e.length + 1

theorem wordPos_of_getElem? [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)} {x : ℕ}
    {z : (α × Bool) × Block} (h : (labelledWord e w)[x]? = some z) :
    wordPos e w x = blockPos e.length z.2 := by
  rw [wordPos, h]

theorem wordPos_of_none [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)} {x : ℕ}
    (h : (labelledWord e w)[x]? = none) : wordPos e w x = 3 * e.length + 1 := by
  rw [wordPos, h]

theorem wordPos_le [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) (x : ℕ) :
    wordPos e w x ≤ 3 * e.length + 1 := by
  rcases hx : (labelledWord e w)[x]? with _ | z
  · rw [wordPos_of_none hx]
  · rw [wordPos_of_getElem? hx]
    have hmem : blockPos e.length z.2
        ∈ (labelledWord e w).map (fun y => blockPos e.length y.2) :=
      List.mem_map_of_mem (List.mem_of_getElem? hx)
    have := map_blockPos_labelledWord_le e w _ hmem
    omega

/-- **The labelling is monotone.**  Inside the word this is
`pairwise_map_blockPos_labelledWord`; past the end the value is `3n + 1`, which
`wordPos_le` puts above everything. -/
theorem wordPos_monotone [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    ∀ x y : ℕ, x ≤ y → wordPos e w x ≤ wordPos e w y := by
  intro x y hxy
  rcases hy : (labelledWord e w)[y]? with _ | zy
  · rw [wordPos_of_none hy]
    exact wordPos_le e w x
  · have hylt : y < (labelledWord e w).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hy
      simp at hy
    have hxlt : x < (labelledWord e w).length := by omega
    have hx : (labelledWord e w)[x]? = some ((labelledWord e w)[x]'hxlt) :=
      List.getElem?_eq_getElem hxlt
    have hy' : (labelledWord e w)[y]'hylt = zy := by
      rw [List.getElem?_eq_getElem hylt] at hy
      exact Option.some.inj hy
    rw [wordPos_of_getElem? hx, wordPos_of_getElem? hy, ← hy']
    rcases Nat.eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · have hpw := pairwise_map_blockPos_labelledWord e w
      have hmx : x < ((labelledWord e w).map
          (fun z => blockPos e.length z.2)).length := by
        rw [List.length_map]; exact hxlt
      have hmy : y < ((labelledWord e w).map
          (fun z => blockPos e.length z.2)).length := by
        rw [List.length_map]; exact hylt
      have := List.pairwise_iff_getElem.mp hpw x y hmx hmy hlt
      rwa [List.getElem_map, List.getElem_map] at this

/-- **Which blocks occur.**  Every letter of the labelled word carries either a
block of a factor of index `< n`, or the boundary.  This is what makes
`blockPos_injOn` applicable. -/
theorem block_occurs_of_mem_word [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    {z : (α × Bool) × Block} (hz : z ∈ labelledWord e w) :
    (∃ k < e.length,
        z.2 = Block.conj k ∨ z.2 = Block.relator k ∨ z.2 = Block.stem k)
      ∨ z.2 = Block.boundary := by
  rw [labelledWord, List.mem_append] at hz
  rcases hz with h | h
  · obtain ⟨j, -, hjlt, hlab⟩ := index_mem_range_of_mem_labelledExpr 0 e z h
    exact Or.inl ⟨j, by omega, hlab⟩
  · exact Or.inr (snd_eq_of_mem_tag h)

/-! ## 4.  The two ends of a pair get different blocks -/

/-- **The bridge from positions to values.**  At the two ends of a matched pair,
`wordPos` reads the blocks of that pair's two entries.

This is what lets `MatchingSameBlock`'s theorem — which speaks about `T.pairs` —
be spent on a hypothesis about `T.pairIdx`. -/
theorem wordPos_eq_of_mem_pairIdx [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    {i j : ℕ} (h : (i, j) ∈ T.pairIdx) :
    ∃ p ∈ T.pairs, wordPos e w i = blockPos e.length (p.1).2 ∧
      wordPos e w j = blockPos e.length (p.2).2 := by
  obtain ⟨a, b, A, P, S, hp, hw, hlen, hj⟩ :=
    DTree.exists_block_of_mem_pairIdx T i j h
  refine ⟨(a, b), hp, ?_, ?_⟩
  · refine wordPos_of_getElem? ?_
    rw [← hT, ← List.head?_drop, hw, ← hlen, List.drop_left]
    rfl
  · refine wordPos_of_getElem? ?_
    rw [← hT, ← List.head?_drop]
    have hw2 : T.word = (P ++ (a :: A.word)) ++ (b :: S) := by
      rw [hw]
      simp only [List.cons_append, List.append_assoc]
    have hlen2 : (P ++ (a :: A.word)).length = j := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [hw2, ← hlen2, List.drop_left]
    rfl

/-- **The two ends of a matched pair get different values.**  The blocks differ
(`MatchingSameBlock.block_ne_of_mem_pairs_labelledWord`) and `blockPos` separates
the blocks that occur, so the chord it produces is a genuine chord.

This is the second hypothesis `MatchingChordGraph` asks for, discharged. -/
theorem wordPos_ne_of_mem_pairIdx [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hrel : ∀ q ∈ e, FreeGroup.IsReduced q.2) (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ q ∈ T.pairIdx, wordPos e w q.1 ≠ wordPos e w q.2 := by
  intro q hq heq
  obtain ⟨p, hp, h1, h2⟩ :=
    wordPos_eq_of_mem_pairIdx hT (i := q.1) (j := q.2) (by simpa using hq)
  have hbne : (p.1).2 ≠ (p.2).2 :=
    block_ne_of_mem_pairs_labelledWord hrel hw hT hmatch p hp
  refine hbne (blockPos_injOn ?_ ?_ (by rw [← h1, ← h2]; exact heq))
  · refine block_occurs_of_mem_word (e := e) (w := w) ?_
    rw [← hT]
    exact DTree.fst_mem_word hp
  · refine block_occurs_of_mem_word (e := e) (w := w) ?_
    rw [← hT]
    exact DTree.snd_mem_word hp


/-! ## 5.  The degree bound, with the labelling discharged -/

/-- The boundary block is a vertex, as soon as `w` is nonempty. -/
theorem boundary_mem_posSet [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hwne : w ≠ []) {T : DTree ((α × Bool) × Block)}
    (hT : T.word = labelledWord e w) :
    3 * e.length ∈ DTree.posSet T (wordPos e w) := by
  have hinv : FreeGroup.invRev w ≠ [] := by
    intro hcon
    refine hwne ?_
    have := congrArg List.length hcon
    rw [FreeGroup.invRev_length, List.length_nil] at this
    exact List.length_eq_zero_iff.mp this
  obtain ⟨y, ys, hys⟩ : ∃ y ys, FreeGroup.invRev w = y :: ys := by
    rcases hcase : FreeGroup.invRev w with _ | ⟨y, ys⟩
    · exact absurd hcase hinv
    · exact ⟨y, ys, rfl⟩
  have hhead : (labelledWord e w)[(exprWord e).length]?
      = some (y, Block.boundary) := by
    rw [← List.head?_drop, ← length_labelledExpr 0 e, labelledWord,
      List.drop_left, tag, hys]
    rfl
  have hx : (exprWord e).length < T.word.length := by
    rw [hT, length_labelledWord]
    have : 0 < w.length := List.length_pos_iff.mpr hwne
    omega
  have hval : wordPos e w (exprWord e).length = 3 * e.length := by
    rw [wordPos_of_getElem? hhead]
    rfl
  rw [← hval]
  exact DTree.pos_mem_posSet hx

/-- A second vertex, as soon as the expression part is nonempty: the first letter
of the word carries a factor block, whose value is at most `3n − 1`. -/
theorem two_le_card_posSet [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hexpr : labelledExpr 0 e ≠ []) (hwne : w ≠ [])
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w) :
    2 ≤ (DTree.posSet T (wordPos e w)).card := by
  have hlenpos : 0 < (labelledExpr 0 e).length :=
    List.length_pos_iff.mpr hexpr
  have h0 : (labelledWord e w)[0]? = (labelledExpr 0 e)[0]? := by
    rw [labelledWord]
    exact List.getElem?_append_left hlenpos
  obtain ⟨z, hz⟩ : ∃ z, (labelledExpr 0 e)[0]? = some z :=
    ⟨(labelledExpr 0 e)[0]'hlenpos, List.getElem?_eq_getElem hlenpos⟩
  have hzmem : z ∈ labelledExpr 0 e := List.mem_of_getElem? hz
  have hval : wordPos e w 0 = blockPos e.length z.2 := by
    refine wordPos_of_getElem? ?_
    rw [h0]
    exact hz
  have hbound : blockPos e.length z.2 < 3 * e.length := by
    have hmem : blockPos e.length z.2
        ∈ (labelledExpr 0 e).map (fun y => blockPos e.length y.2) :=
      List.mem_map_of_mem hzmem
    obtain ⟨-, h2⟩ := map_blockPos_labelledExpr_bounds e.length 0 e _ hmem
    omega
  have h0lt : 0 < T.word.length := by
    rw [hT, length_labelledWord]
    have hle : (labelledExpr 0 e).length = (exprWord e).length :=
      length_labelledExpr 0 e
    omega
  refine Finset.one_lt_card.mpr ⟨wordPos e w 0, DTree.pos_mem_posSet h0lt,
    3 * e.length, boundary_mem_posSet hwne hT, ?_⟩
  rw [hval]
  omega

/-- **The degree bound on the labelled word, with no hypothesis left about the
labelling.**  Some block other than the boundary is matched into at most four
blocks.

What this does *not* say — see `CurvatureStemThreshold` — is that the block it
returns is a *relator* block.  With the conjugator blocks present as vertices the
count does not close, and the block handed back may be a `conj` or `stem` block.
The chord machinery is unconditional; the stem problem is untouched. -/
theorem exists_block_degree_le_four [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hrel : ∀ q ∈ e, FreeGroup.IsReduced q.2) (hw : FreeGroup.IsReduced w)
    (hexpr : labelledExpr 0 e ≠ []) (hwne : w ≠ [])
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∃ v ∈ (DTree.posSet T (wordPos e w)).erase (3 * e.length),
      (NonCrossing.star (DTree.chordSet T (wordPos e w)) v).card ≤ 4 :=
  DTree.exists_vertex_degree_le_four (wordPos_monotone e w)
    (wordPos_ne_of_mem_pairIdx hrel hw hT hmatch)
    (boundary_mem_posSet hwne hT) (two_le_card_posSet hexpr hwne hT)

end SmallCancellationRouter
end GroupApproximation
