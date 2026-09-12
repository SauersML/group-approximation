import GroupApproximation.Sofic.MatchingBlockOrder
import GroupApproximation.Sofic.MatchingFactorPair

/-!
# The edge bound at factor resolution: `|E| + 1 ≤ 2n`

`CurvatureStemThreshold` records that the curvature count cannot close while the
conjugator and stem blocks are vertices of the run graph: `labelledWord` has
three blocks per factor, so the outerplanar bound runs at `V = 3n + 1` and gives
only `e ≤ 6n − 1`, which the "seven runs per interior region" hypothesis does not
contradict.  The remedy considered there — contracting each factor to one vertex
— was set aside because it **sells the metric condition**: a run between two
contracted factors is a common subword of two palindromes, not of two relators,
so it need not be a piece.

That objection is about the **run bound**, and the count needs two separate
things from the planar side.  The **edge bound** is not affected, and this module
supplies it at factor resolution:

    `chordSet_card_add_one_le_two_mul_length : (chordSet T (factorWordPos e w)).card + 1 ≤ 2 * e.length`

which is `one_shell_of_counts`'s hypothesis `hE : e + 1 ≤ 2 * n` on the nose.
Nothing here is new mathematics; the whole file is a re-instantiation of machinery
that is already green.

## Why it is a re-instantiation and not a new argument

`MatchingChordGraph` is parametric in an arbitrary `pos : ℕ → ℕ` and asks for
exactly two things — monotonicity, and that the two ends of a matched pair get
different values.  At factor resolution both are already available:

* `blockPos` sends the three blocks of factor `k` to `3k`, `3k+1`, `3k+2` and the
  boundary to `3n`.  So factor resolution is literally `wordPos e w x / 3`
  (`blockPos_div_three`), and monotonicity is `wordPos_monotone` composed with
  `Nat.div_le_div_right`;
* the two ends of a pair lie in different **factors** —
  `MatchingFactorPair.factor_ne_of_mem_pairs_labelledWord`, which needs only that
  each factor is a reduced palindrome and that `w` is reduced — and
  `MatchingBlockOrder.wordPos_eq_of_mem_pairIdx` is the bridge from positions to
  pairs.

The gain is the vertex count: `posSet` at factor resolution lands in
`{0, …, n}`, so `NonCrossingEdgeBound.card_add_three_le_two_mul_card` gives
`|E| + 3 ≤ 2(n+1)`, which is `|E| + 1 ≤ 2n`.

What this module does **not** do is bound the runs.  With the factors contracted
a run may pair a relator letter with a conjugator letter, and `C'(λ)` says
nothing about such a run; that is the fold, and it is still open.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The factor a block belongs to -/

/-- **The factor index of a block**, with the boundary sent past every factor.
This is `blockPos` with the three blocks of a factor identified. -/
def factorIndex (n : ℕ) : Block → ℕ
  | Block.conj k => k
  | Block.relator k => k
  | Block.stem k => k
  | Block.boundary => n

@[simp] theorem factorIndex_conj (n k : ℕ) :
    factorIndex n (Block.conj k) = k := rfl

@[simp] theorem factorIndex_relator (n k : ℕ) :
    factorIndex n (Block.relator k) = k := rfl

@[simp] theorem factorIndex_stem (n k : ℕ) :
    factorIndex n (Block.stem k) = k := rfl

@[simp] theorem factorIndex_boundary (n : ℕ) :
    factorIndex n Block.boundary = n := rfl

/-- **Factor resolution is block resolution divided by three.**  The three blocks
of factor `k` occupy `3k`, `3k+1`, `3k+2`, so integer division by three contracts
each factor to a single vertex and leaves the boundary where it was. -/
theorem blockPos_div_three (n : ℕ) (b : Block) :
    blockPos n b / 3 = factorIndex n b := by
  cases b with
  | conj k => simp only [blockPos_conj, factorIndex_conj]; omega
  | relator k => simp only [blockPos_relator, factorIndex_relator]; omega
  | stem k => simp only [blockPos_stem, factorIndex_stem]; omega
  | boundary => simp only [blockPos_boundary, factorIndex_boundary]; omega

/-- A block of a factor carries that factor's index, and its `factor` field
names it.  Packaged so that the three-way disjunction
`block_occurs_of_mem_word` produces is consumed once. -/
theorem factorIndex_eq_of_occurs {n k : ℕ} {b : Block}
    (h : b = Block.conj k ∨ b = Block.relator k ∨ b = Block.stem k) :
    factorIndex n b = k ∧ b.factor = some k := by
  rcases h with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-! ## 2.  The factor-resolution labelling -/

/-- **The factor at a position.**  `MatchingChordGraph` is parametric in the
labelling, and this is `wordPos` read at factor resolution. -/
def factorWordPos [DecidableEq α] (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) (x : ℕ) : ℕ :=
  wordPos e w x / 3

theorem factorWordPos_of_getElem? [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)} {x : ℕ}
    {z : (α × Bool) × Block} (h : (labelledWord e w)[x]? = some z) :
    factorWordPos e w x = factorIndex e.length z.2 := by
  rw [factorWordPos, wordPos_of_getElem? h, blockPos_div_three]

/-- **Monotone**, the first hypothesis of the chord graph: `wordPos` is monotone
and division by three preserves that. -/
theorem factorWordPos_monotone [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    ∀ x y : ℕ, x ≤ y → factorWordPos e w x ≤ factorWordPos e w y := by
  intro x y hxy
  exact Nat.div_le_div_right (wordPos_monotone e w x y hxy)

/-- **Every vertex is a factor index or the boundary.**  This is the whole gain:
at block resolution the bound is `3n + 1`, here it is `n`. -/
theorem factorWordPos_le [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) (x : ℕ) :
    factorWordPos e w x ≤ e.length := by
  have h := wordPos_le e w x
  simp only [factorWordPos]
  omega

/-! ## 3.  The two ends of a pair lie in different factors -/

/-- **The second hypothesis of the chord graph, at factor resolution.**  The two
ends of a matched pair lie in different factors -- that is
`MatchingFactorPair.factor_ne_of_mem_pairs_labelledWord`, whose only inputs are
that each factor is a reduced palindrome and that `w` is reduced -- and the
boundary is separated from every factor because factor indices are `< n` while
the boundary is `n`. -/
theorem factorWordPos_ne_of_mem_pairIdx [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hred : ∀ q ∈ e, FreeGroup.IsReduced
      (q.1.toWord ++ (q.2 ++ FreeGroup.invRev q.1.toWord)))
    (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ q ∈ T.pairIdx, factorWordPos e w q.1 ≠ factorWordPos e w q.2 := by
  intro q hq heq
  obtain ⟨p, hp, h1, h2⟩ :=
    wordPos_eq_of_mem_pairIdx hT (i := q.1) (j := q.2) (by simpa using hq)
  have hfne : ((p.1).2).factor ≠ ((p.2).2).factor :=
    factor_ne_of_mem_pairs_labelledWord hred hw hT hmatch p hp
  have hidx : factorIndex e.length (p.1).2 = factorIndex e.length (p.2).2 := by
    simp only [factorWordPos] at heq
    rw [h1, h2, blockPos_div_three, blockPos_div_three] at heq
    exact heq
  have hocc1 := block_occurs_of_mem_word (e := e) (w := w) (z := p.1)
    (by rw [← hT]; exact DTree.fst_mem_word hp)
  have hocc2 := block_occurs_of_mem_word (e := e) (w := w) (z := p.2)
    (by rw [← hT]; exact DTree.snd_mem_word hp)
  rcases hocc1 with ⟨k1, hk1, hb1⟩ | hb1 <;> rcases hocc2 with ⟨k2, hk2, hb2⟩ | hb2
  · obtain ⟨hi1, hf1⟩ := factorIndex_eq_of_occurs (n := e.length) hb1
    obtain ⟨hi2, hf2⟩ := factorIndex_eq_of_occurs (n := e.length) hb2
    rw [hi1, hi2] at hidx
    exact hfne (by rw [hf1, hf2, hidx])
  · obtain ⟨hi1, -⟩ := factorIndex_eq_of_occurs (n := e.length) hb1
    rw [hi1, hb2, factorIndex_boundary] at hidx
    omega
  · obtain ⟨hi2, -⟩ := factorIndex_eq_of_occurs (n := e.length) hb2
    rw [hi2, hb1, factorIndex_boundary] at hidx
    omega
  · exact hfne (by rw [hb1, hb2])

/-! ## 4.  The vertex count, and the edge bound -/

/-- **The boundary is a vertex**, transported from block resolution: its block
value is `3n`, so its factor value is `n`. -/
theorem boundary_mem_posSet_factor [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hwne : w ≠ []) {T : DTree ((α × Bool) × Block)}
    (hT : T.word = labelledWord e w) :
    e.length ∈ DTree.posSet T (factorWordPos e w) := by
  obtain ⟨x, hx, hval⟩ := DTree.mem_posSet.mp (boundary_mem_posSet hwne hT)
  refine DTree.mem_posSet.mpr ⟨x, hx, ?_⟩
  simp only [factorWordPos]
  rw [hval]
  omega

/-- **There are at least two vertices**: the boundary, and the factor of the
first letter of the expression. -/
theorem two_le_card_posSet_factor [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hexpr : labelledExpr 0 e ≠ []) (hwne : w ≠ [])
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w) :
    2 ≤ (DTree.posSet T (factorWordPos e w)).card := by
  have hlenpos : 0 < (labelledExpr 0 e).length := List.length_pos_iff.mpr hexpr
  have h0 : (labelledWord e w)[0]? = (labelledExpr 0 e)[0]? := by
    rw [labelledWord]
    exact List.getElem?_append_left hlenpos
  obtain ⟨z, hz⟩ : ∃ z, (labelledExpr 0 e)[0]? = some z :=
    ⟨(labelledExpr 0 e)[0]'hlenpos, List.getElem?_eq_getElem hlenpos⟩
  have hzmem : z ∈ labelledExpr 0 e := List.mem_of_getElem? hz
  have hval : factorWordPos e w 0 = factorIndex e.length z.2 := by
    refine factorWordPos_of_getElem? ?_
    rw [h0]
    exact hz
  have hbound : blockPos e.length z.2 < 3 * e.length := by
    have hmem : blockPos e.length z.2
        ∈ (labelledExpr 0 e).map (fun y => blockPos e.length y.2) :=
      List.mem_map_of_mem hzmem
    obtain ⟨-, hb2⟩ := map_blockPos_labelledExpr_bounds e.length 0 e _ hmem
    omega
  have hlt : factorIndex e.length z.2 < e.length := by
    rw [← blockPos_div_three]
    omega
  have h0lt : 0 < T.word.length := by
    rw [hT, length_labelledWord]
    have hle : (labelledExpr 0 e).length = (exprWord e).length :=
      length_labelledExpr 0 e
    omega
  refine Finset.one_lt_card.mpr ⟨factorWordPos e w 0, DTree.pos_mem_posSet h0lt,
    e.length, boundary_mem_posSet_factor hwne hT, ?_⟩
  rw [hval]
  omega

/-- **Every vertex is at most `n`**, so there are at most `n + 1` of them. -/
theorem card_posSet_factor_le [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    {T : DTree ((α × Bool) × Block)} :
    (DTree.posSet T (factorWordPos e w)).card ≤ e.length + 1 := by
  have hsub : DTree.posSet T (factorWordPos e w) ⊆ Finset.range (e.length + 1) := by
    intro v hv
    obtain ⟨x, -, hvx⟩ := DTree.mem_posSet.mp hv
    rw [Finset.mem_range, ← hvx]
    have := factorWordPos_le e w x
    omega
  have h := Finset.card_le_card hsub
  rwa [Finset.card_range] at h

/-- **The edge bound at factor resolution.**

`one_shell_of_counts`'s hypothesis `hE : e + 1 ≤ 2 * n`, with `n = e.length` the
number of relator blocks.  This is the input `CurvatureStemThreshold` shows is
unavailable while the conjugator and stem blocks are separate vertices. -/
theorem chordSet_card_add_one_le_two_mul_length [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hred : ∀ q ∈ e, FreeGroup.IsReduced
      (q.1.toWord ++ (q.2 ++ FreeGroup.invRev q.1.toWord)))
    (hw : FreeGroup.IsReduced w) (hexpr : labelledExpr 0 e ≠ []) (hwne : w ≠ [])
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    (DTree.chordSet T (factorWordPos e w)).card + 1 ≤ 2 * e.length := by
  have hmono := factorWordPos_monotone e w
  have hne := factorWordPos_ne_of_mem_pairIdx hred hw hT hmatch
  have hbound := NonCrossing.card_add_three_le_two_mul_card
    (DTree.posSet T (factorWordPos e w)) (DTree.chordSet T (factorWordPos e w))
    (DTree.chordSet_ordered hmono hne) DTree.chordSet_mem
    (DTree.chords_not_straddle hmono) (two_le_card_posSet_factor hexpr hwne hT)
  have hcard := card_posSet_factor_le (e := e) (w := w) (T := T)
  omega

/-- **The degree bound at factor resolution**, free from the same instantiation:
some factor other than the boundary meets at most four others.  Unlike
`exists_block_degree_le_four` the vertex handed back is a *factor*, which is what
the curvature count wants -- what it still does not know is that the runs at that
vertex are pieces. -/
theorem exists_factor_degree_le_four [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hred : ∀ q ∈ e, FreeGroup.IsReduced
      (q.1.toWord ++ (q.2 ++ FreeGroup.invRev q.1.toWord)))
    (hw : FreeGroup.IsReduced w) (hexpr : labelledExpr 0 e ≠ []) (hwne : w ≠ [])
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∃ v ∈ (DTree.posSet T (factorWordPos e w)).erase e.length,
      (NonCrossing.star (DTree.chordSet T (factorWordPos e w)) v).card ≤ 4 :=
  DTree.exists_vertex_degree_le_four (factorWordPos_monotone e w)
    (factorWordPos_ne_of_mem_pairIdx hred hw hT hmatch)
    (boundary_mem_posSet_factor hwne hT) (two_le_card_posSet_factor hexpr hwne hT)

end SmallCancellationRouter
end GroupApproximation
