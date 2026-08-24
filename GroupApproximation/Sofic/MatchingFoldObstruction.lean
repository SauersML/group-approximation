import GroupApproximation.Sofic.MatchingChordGraph

/-!
# The naive fold, and why it does not preserve planarity

`CurvatureStemThreshold` shows the curvature count cannot close while the
conjugator blocks are vertices of the run graph, and that the remaining work is a
**fold**: an operation on the matching removing the conjugator letters while
keeping the runs between relator blocks.  There is an obvious candidate.  This
file records what it is, why it produces a legitimate *matching*, and the exact
configuration in which it fails to produce a legitimate *non-crossing* matching.

## The candidate

`ConjExprMatching.labelledFactor` spells factor `k` as
`cₖ ++ (tₖ ++ invRev cₖ)`.  Position `j` of the `conj k` block and position
`|cₖ| − 1 − j` of the `stem k` block carry mutually inverse letters — they are
the two sides of the same edge of the cactus, which folding identifies.  Call
that pairing the **mirror**.  It is nested inside the factor: as the `conj` index
rises the `stem` index falls, and the relator block sits between them.

Now every `conj`/`stem` letter carries exactly one matched pair and exactly one
mirror pair, and every `relator`/`boundary` letter carries a matched pair and no
mirror.  So the union of the two pairings is a disjoint union of paths and
cycles, the paths running between `relator`/`boundary` letters through an
alternating sequence of matched and mirror steps.  Along such a path each step
inverts the letter and the number of steps is odd, so **the two endpoints of a
path carry mutually inverse letters**: the transfer is a perfect matching of the
relator and boundary letters, with no conjugator letter left in it.

That much is right, and it is why the fold looks like the answer.

## Where it fails

The transfer is a matching but **not a non-crossing one**, and the obstruction is
not subtle: folding changes the cyclic order of the boundary walk, and the
transfer is being read in the *old* order.

`transfer_straddles_witness` is the configuration, six positions:

```text
       0     1     2     3     4     5
       y     p     x     u     q     u'
       └───────────────────────────┘      matched  (y, u')
             └─────────────┘              matched  (p, q)
                   └─────┘                matched  (x, u)
                         └───────────┘    mirror   (u, u')
```

The three matched pairs are pairwise non-straddling — they are fully nested — and
the mirror pair `(u, u')` brackets exactly one position, `q`, standing for a
one-letter relator block.  `x` and `y` are the matched partners of `u` and `u'`,
so the transfer replaces `(x, u)` and `(y, u')` by `(y, x) = (0, 2)`.  And
`(0, 2)` straddles `(1, 4)`:

    `0 < 1 < 2 < 4`.

So planarity is lost.  `MatchingPositions.pairIdx_noncrossing` is what every
count in this lane runs on, and the transfer does not deliver it.

## What the configuration means, and what it does not

`q` lies strictly between `u` and `u'`, so `q` is a letter of the relator block
of that very factor, and it is matched to `p`, which lies outside the factor on
the left.  Nothing forbids that: `MatchingFactorPair.factor_ne_of_mem_pairs_labelledWord`
forbids a pair with both ends in one factor, and this pair has one end outside.

What is *not* claimed here is that these six positions occur in an actual
`labelledWord` of an actual minimal expression.  The claim is the one the next
attempt needs: **the transfer is not non-crossing as a general operation on
non-crossing matchings with a nested mirror**, so a fold argument cannot be
completed by combinatorics on the original linear order alone.  Either the
configuration has to be excluded — by minimality, or by the metric condition, or
by some property of the expression not yet spent — or the fold has to be
performed together with the reordering of the boundary walk that folding
actually induces.

Everything below is arithmetic on six numbers.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

/-- **The straddle predicate**, in the form `MatchingPositions.not_straddle`
forbids and `MatchingChordGraph` consumes. -/
def Straddles (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2

instance decidableStraddles (p q : ℕ × ℕ) : Decidable (Straddles p q) := by
  unfold Straddles
  infer_instance

/-- **The three matched pairs of the witness are pairwise non-straddling.**  They
are fully nested: `(2,3) ⊂ (1,4) ⊂ (0,5)`. -/
theorem fold_witness_matching_noncrossing :
    ∀ p ∈ [((0 : ℕ), (5 : ℕ)), (1, 4), (2, 3)],
      ∀ q ∈ [((0 : ℕ), (5 : ℕ)), (1, 4), (2, 3)], ¬ Straddles p q := by
  decide

/-- **The mirror pair brackets exactly the relator block.**  `(u, u') = (3, 5)`
and the only position strictly between them is `4`, which is the one-letter
relator block of that factor.  So the mirror is nested in the factor, as
`labelledFactor` makes it. -/
theorem fold_witness_mirror :
    (3 : ℕ) < 5 ∧ ∀ z : ℕ, 3 < z → z < 5 → z = 4 := by
  refine ⟨by omega, ?_⟩
  intro z h1 h2
  omega

/-- **The transferred pair straddles.**  Folding the mirror `(3, 5)` replaces the
matched pairs `(2, 3)` and `(0, 5)` by the pair joining their far ends, `(0, 2)`
— and `0 < 1 < 2 < 4` says `(0, 2)` straddles `(1, 4)`.

So the naive fold destroys planarity, and every count in this lane runs on
planarity. -/
theorem transfer_straddles_witness : Straddles ((0 : ℕ), (2 : ℕ)) (1, 4) := by
  refine ⟨by omega, by omega, by omega⟩

/-- **The two halves together**, as one statement: a non-crossing matching with a
nested mirror whose transfer is not non-crossing. -/
theorem naive_fold_not_noncrossing :
    (∀ p ∈ [((0 : ℕ), (5 : ℕ)), (1, 4), (2, 3)],
      ∀ q ∈ [((0 : ℕ), (5 : ℕ)), (1, 4), (2, 3)], ¬ Straddles p q) ∧
    Straddles ((0 : ℕ), (2 : ℕ)) (1, 4) :=
  ⟨fold_witness_matching_noncrossing, transfer_straddles_witness⟩

end SmallCancellationRouter
end GroupApproximation
