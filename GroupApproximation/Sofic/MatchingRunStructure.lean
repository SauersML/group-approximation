import GroupApproximation.Sofic.MatchingPositions

/-!
# Two blocks meet in one run, and what that settles

`MatchingPositions` turns the matching into positions and states planarity as an
inequality (`pairIdx_noncrossing`).  This file spends that inequality on the one
structural fact the curvature count has been missing, and the fact is stronger
than expected:

    **`run_contiguous`** — if two letters of a block are matched into the same
    other block, so is every letter between them.

The blocks of `labelledWord` are intervals of the word and no pair joins two
letters of one block, so this says: *the letters of a block matched into a given
other block form one contiguous run*, and a block's arc is therefore a
concatenation of runs, **one per neighbouring block**, in a definite order.

## 1.  What this settles: contiguity is not an extra hypothesis

`CurvatureAssembly.three_arc_shortfall` shows that a region meeting the boundary
in three *separated* arcs defeats the count: `(1 − 3λ)·|r|` spread over three
arcs leaves a longest arc near `(1 − 3λ)·|r|/3`, which at `λ ≤ 1/6` is `|r|/6`
and misses even the half-form.  That arithmetic is correct and stays as a guard
rail.

**What it does not do is describe this model.**  In a general van Kampen diagram
a region may meet `∂D` in several arcs.  Here it cannot: the boundary letters
are one block, an interval of the word, and `run_contiguous` says a relator block
meets that interval in a single run.  So the boundary part of a relator block is
automatically one arc, and after rotating the relator — the symmetrization is
closed under rotation — it reads

    `r = δ ++ p₁ ++ ⋯ ++ p_d`,   `δ` the boundary run, `pᵢ` the interior runs.

That is exactly the shape `CurvatureAssembly.ShellDecomposition` asks for.
**Contiguity is a consequence of planarity plus the block intervals plus the
self-pairing exclusion; it is not something the degree bound has to carry.**

## 2.  What this settles: the basepoint is not a problem either

The classical worry is that a region's boundary arc runs along the *cyclic* word
`w` and may straddle the basepoint, so that `δ <:+: w` fails and one needs two
disjoint shells to be sure of a linear infix.  Here the boundary block is a
contiguous stretch of the **linear** word `labelledWord e w`, so a run inside it
is a contiguous infix of `invRev w`, hence `δ <:+: w` by
`RelatorBlock.infix_of_invRev_infix`.  The basepoint never enters.

So `ShellFromMinimal` is the right target after all, and does not have to be
restated in a two-shell form.

## 3.  What is left, sharply

Two things, and neither is contiguity.

* **The degree bound**, and it is *not* a consequence of planarity alone.  The
  block graph is outerplanar by construction — the runs are non-crossing chords
  with the blocks in cyclic order, so the drawing is the data and no planar map
  has to be reconstructed.  But outerplanarity alone gives only `E ≤ 2V − 3`,
  which does not by itself produce a *boundary* block of small degree.  The
  classical argument closes that gap with `C'(1/6)` itself: every run between two
  relator blocks is a piece, so `6·|run| < |r|`
  (`MatchingRunPiece.six_mul_length_lt_of_relator_run`), so a relator block all of
  whose runs are interior has at least seven of them.  The count then has room.
  That last step is a counting argument over the non-crossing structure — an
  induction over `wrap`, not Euler's formula — and it is the remaining work.
* **The stems.**  A relator block's runs may go to `conj`/`stem` blocks as well
  as to relator blocks and the boundary.  Those runs are contiguous too, so the
  shell *shape* survives, but a run into a conjugator is a common subword of a
  relator and a conjugator, which is **not a piece**, so
  `CurvatureAssembly.InteriorRun` fails for it.  The stems do not break
  contiguity; they break piece-hood.  `MatchingStemContraction` shows they cannot
  simply be deleted.

Unconditional, alphabet-agnostic: no relators, no metric condition, no group.
-/

namespace GroupApproximation
namespace SmallCancellationRouter
namespace DTree

universe u

variable {β : Type u}

/-! ## 1.  A position and its partner -/

/-- Two positions of the word are matched to each other, in whichever order the
tree records them. -/
def MatchedAt (T : DTree β) (m n : ℕ) : Prop :=
  (m, n) ∈ T.pairIdx ∨ (n, m) ∈ T.pairIdx

/-- A matched pair, read with its endpoints in order.  `lt_of_mem_pairIdx` says a
pair always opens before it closes, so the smaller position is the opening
one. -/
theorem mem_pairIdx_of_matchedAt {T : DTree β} {m n : ℕ} (h : T.MatchedAt m n) :
    (min m n, max m n) ∈ T.pairIdx := by
  rcases h with h | h
  · have hb := lt_of_mem_pairIdx h
    rw [min_eq_left (le_of_lt hb.1), max_eq_right (le_of_lt hb.1)]
    exact h
  · have hb := lt_of_mem_pairIdx h
    rw [min_eq_right (le_of_lt hb.1), max_eq_left (le_of_lt hb.1)]
    exact h

theorem MatchedAt.symm {T : DTree β} {m n : ℕ} (h : T.MatchedAt m n) :
    T.MatchedAt n m := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem MatchedAt.ne {T : DTree β} {m n : ℕ} (h : T.MatchedAt m n) : m ≠ n := by
  have hb := lt_of_mem_pairIdx (mem_pairIdx_of_matchedAt h)
  omega

/-! ## 2.  Two blocks meet in one run -/

/-- **Two blocks meet in one run.**

`[bL, bR)` and `[cL, cR)` are two disjoint stretches of the word — two blocks.
If the letters at `i₁` and `i₃` of the first are matched into the second, then so
is the letter at any `i₂` between them.

The only inputs are planarity (`pairIdx_noncrossing`), that the blocks are
*intervals*, and that no pair has both ends in the first block — the last being
what `hnoself` records and what the self-pairing exclusion supplies.

Read as a statement about sets: the letters of one block matched into another
form an interval, so a block's arc is a concatenation of runs with one run per
neighbouring block.  Everything in the header is a corollary of this. -/
theorem run_contiguous {T : DTree β} {bL bR cL cR i₁ i₂ i₃ j₁ j₂ j₃ : ℕ}
    (h₁ : T.MatchedAt i₁ j₁) (h₂ : T.MatchedAt i₂ j₂) (h₃ : T.MatchedAt i₃ j₃)
    (hdisj : bR ≤ cL ∨ cR ≤ bL)
    (hb₁ : bL ≤ i₁) (hb₁' : i₁ < bR) (hb₂ : bL ≤ i₂) (hb₂' : i₂ < bR)
    (hb₃ : bL ≤ i₃) (hb₃' : i₃ < bR)
    (h12 : i₁ < i₂) (h23 : i₂ < i₃)
    (hc₁ : cL ≤ j₁) (hc₁' : j₁ < cR) (hc₃ : cL ≤ j₃) (hc₃' : j₃ < cR)
    (hnoself : ¬ (bL ≤ j₂ ∧ j₂ < bR)) :
    cL ≤ j₂ ∧ j₂ < cR := by
  have p₁ := mem_pairIdx_of_matchedAt h₁
  have p₂ := mem_pairIdx_of_matchedAt h₂
  have p₃ := mem_pairIdx_of_matchedAt h₃
  have q₁ := lt_of_mem_pairIdx p₁
  have q₂ := lt_of_mem_pairIdx p₂
  have q₃ := lt_of_mem_pairIdx p₃
  have n12 := pairIdx_noncrossing T _ _ _ _ p₁ p₂
  have n23 := pairIdx_noncrossing T _ _ _ _ p₂ p₃
  have n13 := pairIdx_noncrossing T _ _ _ _ p₁ p₃
  omega

/-- **A run reverses order.**  Two letters of one block matched into another,
with the second block to the right: the later letter is matched to the earlier
partner.  This is nesting read on a single run, and it is what turns a run into a
subword rather than a set of positions. -/
theorem run_order_reversing {T : DTree β} {bR cL i i' j j' : ℕ}
    (h : T.MatchedAt i j) (h' : T.MatchedAt i' j')
    (hbc : bR ≤ cL) (hi : i < bR) (hi' : i' < bR) (hj : cL ≤ j) (hj' : cL ≤ j')
    (hii : i < i') : j' < j := by
  have p := mem_pairIdx_of_matchedAt h
  have p' := mem_pairIdx_of_matchedAt h'
  have q := lt_of_mem_pairIdx p
  have q' := lt_of_mem_pairIdx p'
  have n := pairIdx_noncrossing T _ _ _ _ p p'
  omega

end DTree
end SmallCancellationRouter
end GroupApproximation
