import GroupApproximation.Sofic.MatchingPositions
import GroupApproximation.Sofic.NonCrossingDegreeBound

/-!
# The matching's chords, and the degree bound read on them

`NonCrossingDegreeBound` proves that a non-crossing chord diagram on `V` points
of `ℕ`, all but one of which are faces, has a face of degree at most four.
`MatchingPositions` proves that the matched pairs of a `DTree` never straddle.
This file joins them: **the matching's pairs, read through any monotone
labelling of positions, are a non-crossing chord set, and the degree bound
applies to it.**

## The one input

A function `pos : ℕ → ℕ` sending each position of the word to the *block* it
lies in, subject to exactly one condition:

    `pos` is monotone.

That is all "the blocks are intervals, in order" amounts to once it is stated
positionally, and `ConjExprMatching`'s `labelledWord` satisfies it by
construction — the word is `conj 1`, `relator 1`, `stem 1`, …, `boundary`, one
contiguous stretch each, in that order.

Monotone is enough because the only use is its *contrapositive*:
`pos x < pos y → x < y` (`lt_of_pos_lt`).  Chords cross only if the pairs
underneath them cross, and `MatchingPositions.not_straddle` forbids that.  So

    `chords_not_straddle` — no two chords of `chordSet` straddle

is five lines, and no new geometry is introduced: the planarity is the same
planarity, read at a coarser resolution.

## The second input, and where it comes from

`chordSet`'s chords must be **ordered**, `p.1 < p.2`, and monotonicity alone
gives only `≤`.  The strictness is exactly

    no matched pair has both ends in one block,

which is `MatchingSameBlock.block_ne_of_mem_pairs_labelledWord` for the blocks
and `MatchingFactorPair.factor_ne_of_mem_pairs_labelledWord` for whole factors.
It is a hypothesis here (`hne`) because it is a fact about the labelled word, not
about the tree.

## The conclusion

`exists_vertex_degree_le_four` — for any monotone `pos` with no self-pairs, and
any distinguished block `v₀`, some *other* block meets at most four blocks.

Instantiated at `labelledWord e w` with `v₀` the boundary block: **some relator
block is matched into at most four other blocks.**  Since the letters of a block
matched into a given other block are contiguous
(`MatchingRunStructure.run_contiguous`), those at most four blocks cut the
relator into at most four runs, one of them the boundary run — which is the
shell.

What is still not here: the instantiation.  `pos` has to be built for
`labelledWord` and its monotonicity proved, and the passage from "at most four
neighbouring blocks" to the split `r = δ ++ p₁ ++ p₂ ++ p₃` has to be made.
Nothing here discharges `CurvatureAssembly.ShellGate`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u

namespace DTree

variable {β : Type u}

/-! ## 1.  Monotone labellings reflect order -/

/-- **A monotone labelling reflects strict order.**  The only property of `pos`
the chord argument uses: if two positions get different blocks in increasing
order, the positions themselves are in increasing order. -/
theorem lt_of_pos_lt {pos : ℕ → ℕ} (hmono : ∀ x y : ℕ, x ≤ y → pos x ≤ pos y)
    {x y : ℕ} (h : pos x < pos y) : x < y := by
  by_contra hcon
  have hle : y ≤ x := by omega
  have := hmono y x hle
  omega

/-! ## 2.  The chords -/

/-- **The block a position lies in, as a vertex of the chord diagram.**  The
image of `pos` over the positions of the word. -/
def posSet (T : DTree β) (pos : ℕ → ℕ) : Finset ℕ :=
  ((List.range T.word.length).map pos).toFinset

theorem mem_posSet {T : DTree β} {pos : ℕ → ℕ} {v : ℕ} :
    v ∈ posSet T pos ↔ ∃ x < T.word.length, pos x = v := by
  rw [posSet, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, hv⟩
    exact ⟨x, List.mem_range.mp hx, hv⟩
  · rintro ⟨x, hx, hv⟩
    exact ⟨x, List.mem_range.mpr hx, hv⟩

theorem pos_mem_posSet {T : DTree β} {pos : ℕ → ℕ} {x : ℕ}
    (hx : x < T.word.length) : pos x ∈ posSet T pos :=
  mem_posSet.mpr ⟨x, hx, rfl⟩

/-- **The chords of the matching**, one per matched pair, read as a pair of
blocks.  Distinct pairs joining the same two blocks give the same chord, which is
exactly right: two blocks meet in one maximal run
(`MatchingRunGap.run_no_gap`), and the chord counts the run, not its letters. -/
def chordSet (T : DTree β) (pos : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (T.pairIdx.map fun q => (pos q.1, pos q.2)).toFinset

theorem mem_chordSet {T : DTree β} {pos : ℕ → ℕ} {p : ℕ × ℕ} :
    p ∈ chordSet T pos ↔ ∃ q ∈ T.pairIdx, (pos q.1, pos q.2) = p := by
  rw [chordSet, List.mem_toFinset, List.mem_map]

/-- Chords are ordered: a pair opens before it closes, and the two ends lie in
different blocks. -/
theorem chordSet_ordered {T : DTree β} {pos : ℕ → ℕ}
    (hmono : ∀ x y : ℕ, x ≤ y → pos x ≤ pos y)
    (hne : ∀ q ∈ T.pairIdx, pos q.1 ≠ pos q.2) :
    ∀ p ∈ chordSet T pos, p.1 < p.2 := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_chordSet.mp hp
  have hlt : q.1 < q.2 := by
    have := lt_of_mem_pairIdx (T := T) (i := q.1) (j := q.2) (by simpa using hq)
    exact this.1
  have hle : pos q.1 ≤ pos q.2 := hmono _ _ (le_of_lt hlt)
  have hnee : pos q.1 ≠ pos q.2 := hne q hq
  rw [← hpq]
  exact lt_of_le_of_ne hle hnee

/-- Both ends of a chord are blocks of the word. -/
theorem chordSet_mem {T : DTree β} {pos : ℕ → ℕ} :
    ∀ p ∈ chordSet T pos, p.1 ∈ posSet T pos ∧ p.2 ∈ posSet T pos := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_chordSet.mp hp
  have hb := lt_of_mem_pairIdx (T := T) (i := q.1) (j := q.2) (by simpa using hq)
  rw [← hpq]
  exact ⟨pos_mem_posSet (by omega), pos_mem_posSet hb.2⟩

/-- **No two chords straddle.**  The same planarity, read at the resolution of
blocks: chords cross only if the pairs beneath them cross, and
`MatchingPositions.not_straddle` says they do not. -/
theorem chords_not_straddle {T : DTree β} {pos : ℕ → ℕ}
    (hmono : ∀ x y : ℕ, x ≤ y → pos x ≤ pos y) :
    ∀ p ∈ chordSet T pos, ∀ p' ∈ chordSet T pos,
      ¬ (p.1 < p'.1 ∧ p'.1 < p.2 ∧ p.2 < p'.2) := by
  intro p hp p' hp' hstr
  obtain ⟨q, hq, hpq⟩ := mem_chordSet.mp hp
  obtain ⟨q', hq', hpq'⟩ := mem_chordSet.mp hp'
  rw [← hpq, ← hpq'] at hstr
  obtain ⟨h1, h2, h3⟩ := hstr
  refine not_straddle (T := T) (i := q.1) (j := q.2) (k := q'.1) (l := q'.2)
    (by simpa using hq) (by simpa using hq') ?_
  exact ⟨lt_of_pos_lt hmono h1, lt_of_pos_lt hmono h2, lt_of_pos_lt hmono h3⟩

/-! ## 3.  The degree bound, on the matching -/

/-- **Some block other than the distinguished one meets at most four blocks.**

`NonCrossingDegreeBound.exists_degree_le_four` read on the matching: the vertices
are the blocks, the chords are the pairs, and the distinguished block `v₀` is the
one the count does not get to choose — the boundary of the diagram.

Instantiated at `ConjExprMatching.labelledWord`, this is the degree bound: some
relator block is matched into at most four other blocks, and since a block's
letters matched into a given other block are contiguous, that cuts its boundary
into at most four runs. -/
theorem exists_vertex_degree_le_four {T : DTree β} {pos : ℕ → ℕ}
    (hmono : ∀ x y : ℕ, x ≤ y → pos x ≤ pos y)
    (hne : ∀ q ∈ T.pairIdx, pos q.1 ≠ pos q.2)
    {v₀ : ℕ} (hv₀ : v₀ ∈ posSet T pos) (h2 : 2 ≤ (posSet T pos).card) :
    ∃ v ∈ (posSet T pos).erase v₀,
      (NonCrossing.star (chordSet T pos) v).card ≤ 4 := by
  refine NonCrossing.exists_degree_le_four (S := posSet T pos)
    (chordSet_ordered hmono hne) chordSet_mem (chords_not_straddle hmono) ?_ ?_
  · rw [Finset.card_erase_of_mem hv₀]
    omega
  · rw [Finset.card_erase_of_mem hv₀]
    omega

end DTree

end SmallCancellationRouter
end GroupApproximation
