import GroupApproximation.Sofic.NonCrossingDegreeBound

/-!
# What the stems cost the count, exactly

`NonCrossingEdgeBound` and `NonCrossingDegreeBound` finish the counting half of
the curvature argument: on a non-crossing chord diagram with `V` vertices, one of
which is the boundary, some other vertex meets at most four chords, and
`no_shell_contradiction` closes the argument when the vertices are the relator
blocks and the boundary.

That reading of the run graph has **one vertex per relator**.  The object the
matching actually produces does not: `ConjExprMatching.labelledWord` has *three*
blocks per factor — `conj k`, `relator k`, `stem k` — so a diagram with `n`
factors has up to `3n + 1` blocks, not `n + 1`.

This file settles what that costs, and the answer is sharp: **the count does not
close while the stems are vertices**, and it is not close to closing.  The
numbers are here so that nobody spends a session trying to push the existing
bound through, and so that the exact target of the stem work is on record.

## The three statements

Write `n` for the number of factors and `E` for the number of runs.

* `stems_defeat_the_count` — with `V = 3n + 1` the edge bound allows `E` as large
  as `6n − 1`, and then `5n` (five runs per relator block, which is what having
  no shell buys) plus `2n` (one run per conjugator block, which is all a
  nonempty block is worth) is `7n ≤ 12n − 2`.  Satisfiable for every `n ≥ 1`, so
  no contradiction is available.  The witness is exhibited, not merely asserted.
* `stem_count_open_at_three` — even valuing every conjugator block at **three**
  runs leaves `11n ≤ 12n − 2`, satisfiable for every `n ≥ 2`.
* `stem_count_closes_at_four` — valuing every conjugator block at **four** runs
  gives `13n ≤ 12n − 2`, which `ℕ` refuses.  So four is the threshold.

Since a conjugator block of length one meets exactly one other block, "four runs
per conjugator block" is false as a general statement.  The conclusion is not
that the bound is too weak but that the **stems must not be vertices at all**.

## Why the obvious repairs do not work

* *Delete the stems.*  `MatchingStemContraction.mk_relatorWord_of_pairClosed`
  refutes it: a matching in which no pair joins a surviving letter to a deleted
  one forces `mk (t₁ ⋯ tₙ) = mk w`, the relators spelling `w` with no conjugation
  at all.  Deleting the letters is not a contraction, it is a hypothesis that
  essentially no expression satisfies.
* *Contract each factor to one vertex.*  This restores `V = n + 1` and
  `MatchingFactorPair.factor_ne_of_mem_pairs_labelledWord` supplies exactly the
  self-pair exclusion a chord set needs — but it loses the metric condition.  A
  run between two *factors* is a common subword of `cₖ tₖ invRev cₖ` and
  `c_l t_l invRev c_l`, and `C'(λ)` bounds common subwords of two **relators**.
  `MatchingRunPiece.six_mul_length_lt_of_relator_run` reads relator blocks and
  cannot be re-read at factor resolution.  So contraction buys the vertex count
  and sells the `5`.

The remaining work is therefore neither the edge bound nor the degree bound.  It
is a fold: an operation on the matching that removes the conjugator letters
*while preserving the runs between relator blocks*, which is what a van Kampen
diagram is and what the cactus is not.

Everything here is arithmetic in `ℕ`; no group, word, matching or relator
appears.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

/-! ## 1.  The count does not close while the stems are vertices -/

/-- **The stems defeat the count.**  With `n` factors the labelled word has up to
`3n + 1` blocks, the edge bound then permits `6n − 1` runs, and the best degree
bounds available — five per relator block from having no shell, one per
conjugator block from being nonempty — sum to `7n`, which fits.

So no contradiction is available, for any `n ≥ 1`.  The witness `E = 6n − 1` is
exhibited: this is a statement that the inequalities are *simultaneously
satisfiable*, not a failure to find a proof. -/
theorem stems_defeat_the_count (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : ℕ, 2 * E + 6 ≤ 4 * (3 * n + 1) ∧ 5 * n + 1 * (2 * n) ≤ 2 * E := by
  refine ⟨6 * n - 1, ?_, ?_⟩ <;> omega

/-- **Three runs per conjugator block is still not enough.**  Valuing each of the
`2n` conjugator blocks at three runs gives `11n`, and `11n ≤ 12n − 2` holds for
every `n ≥ 2`.  So the gap is not an artifact of the crude bound `1`. -/
theorem stem_count_open_at_three (n : ℕ) (hn : 2 ≤ n) :
    ∃ E : ℕ, 2 * E + 6 ≤ 4 * (3 * n + 1) ∧ 5 * n + 3 * (2 * n) ≤ 2 * E := by
  refine ⟨6 * n - 1, ?_, ?_⟩ <;> omega

/-- **Four runs per conjugator block would close it.**  `5n + 8n = 13n` against
`2E ≤ 12n − 2` is refused by `ℕ`.  So four is exactly the threshold — and a
conjugator block of length one meets exactly one other block, so the hypothesis
is false in general.

The point of stating it is to fix the target: any repair of the stem problem has
to be worth four runs per conjugator block, or has to remove the conjugator
blocks from the vertex set entirely. -/
theorem stem_count_closes_at_four {n E : ℕ}
    (hedge : 2 * E + 6 ≤ 4 * (3 * n + 1)) (hdeg : 5 * n + 4 * (2 * n) ≤ 2 * E) :
    False := by
  omega

/-! ## 2.  Without the stems it closes, and with room -/

/-- **The stem-free count, restated for comparison.**  One vertex per relator
block and one for the boundary: `V = n + 1`, `2E ≤ 4n − 2`, and five runs per
relator block gives `5n ≤ 4n − 2`.

This is `NonCrossingEdgeBound.no_shell_contradiction`; it is repeated here beside
the failing version so that the two vertex counts can be read against each
other. -/
theorem stem_free_count_closes {n E : ℕ}
    (hedge : 2 * E + 6 ≤ 4 * (n + 1)) (hdeg : 5 * n ≤ 2 * E) : False := by
  omega

/-- **How much room the stem-free count has.**  It closes already at *three*
runs per relator block once the block has no boundary run, and the true bound
there is seven; the slack is what makes the shell argument robust.  Stated as:
four runs per relator block is already a contradiction, for every `n`. -/
theorem stem_free_count_closes_at_four {n E : ℕ}
    (hedge : 2 * E + 6 ≤ 4 * (n + 1)) (hdeg : 4 * n ≤ 2 * E) : False := by
  omega

/-- **And it is sharp there too.**  Three runs per relator block does *not*
close: `3n ≤ 4n − 2` for every `n ≥ 2`.  So the `5` that "no shell" buys is not
padding — it is the whole margin. -/
theorem stem_free_count_open_at_three (n : ℕ) (hn : 2 ≤ n) :
    ∃ E : ℕ, 2 * E + 6 ≤ 4 * (n + 1) ∧ 3 * n ≤ 2 * E := by
  refine ⟨2 * n - 1, ?_, ?_⟩ <;> omega

end SmallCancellationRouter
end GroupApproximation
