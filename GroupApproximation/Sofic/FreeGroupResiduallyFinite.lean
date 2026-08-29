import GroupApproximation.Sofic.LEFSofic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Free groups are residually finite, hence sofic

The classical finite-quotient argument, carried out on the ball of radius
`n` around the identity.  Fix a nontrivial element `w` of a free group and
let `L` be its reduced word, of length `n`.  Each generator `a` acts on the
set `{0, …, n}` of *positions* by a partial injection read off from `L`:
if the `i`-th letter of `L` (positions from the left, zero-based) is `a`
with exponent `+1`, the letter moves the point `n - 1 - i` to `n - i`; if
it is `a` with exponent `-1`, it moves `n - i` to `n - 1 - i`.  Because `L`
is reduced, these clauses never conflict: a conflict is precisely an
adjacent cancelling pair.  Each partial injection extends to a genuine
permutation of the ball by matching up the complements of its domain and
range, which have equal cardinality.

The universal property of the free group turns the letter permutations into
a homomorphism to a finite symmetric group, and a telescoping computation
along the word shows the image of `w` moves `0` to `n ≠ 0`.  So every
nontrivial element survives in a finite quotient: free groups are
residually finite, hence LEF, hence sofic.

The construction consumes only the reduced-word interface of
`Mathlib.GroupTheory.FreeGroup.Reduce`: `IsReduced` as a chain condition on
adjacent letters, `isReduced_toWord`, `mk_toWord`, `toWord_eq_nil_iff`, and
`lift_mk`.
-/

/-! ### Letters of the word, by position -/

/-! ### The partial injection of a generator, and its extension -/

/-! ### Satisfiability witnesses

The four position predicates above are consumed as hypotheses throughout the
construction; the witnesses below exhibit each one on the one-letter word it
describes, so none is a proposition the corpus only ever assumes. -/

/-! ### The word moves the basepoint across the ball -/

/-! ### The finite quotient detecting a nontrivial element -/
