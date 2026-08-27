import GroupApproximation.Sofic.GreendlingerLanding

/-!
# A subword beyond the block, and the three ways to find one

`GreendlingerCascade` reduces the gate to `CascadeLanding`, and
`GreendlingerLanding` shows that hypothesis is a weakening of the confinement
one and supplies the arithmetic for following a block past a factor.  What is
still missing is a *reason* the search terminates.  This file supplies the
predicate the search is really about and the three moves that establish it.

## The predicate

`SubwordBeyond R b V` --- the word `V` carries a Greendlinger subword beginning
at or after position `b`.  This is exactly what the descent's inheritance step
consumes (`GreendlingerThreeFactor.greendlingerAt_inherit`), and it is what
`TailSubwordBeyondBlock` asks for, with the position taken to be the length of
the block.  `GreendlingerAt.mono` makes the two interchangeable
(`tailSubwordBeyond_of_subwordBeyond`).

## The three moves

At the factor a block of length `b` arrives at --- palindrome `c' t' invRev c'`,
keeping `P''` and losing `M''` to what follows --- exactly one of three things
happens, and each has its own move.

* **It keeps enough.**  If what the factor keeps beyond the block is more than
  half of its rotation --- `2(k + (b - |c'|)) < |t'|`, where `k` bounds what the
  factor's own block eats past its trailing conjugator --- then the factor
  itself delivers the subword, at position exactly `b`.  That is
  `subwordBeyond_of_keeps`, and it is `greendlingerAt_of_bounded_cancellation`
  read with the offset spent on the block instead of on slack.

* **The block overruns it.**  If `|P''| ≤ b` the block is longer than everything
  the factor keeps, so it reaches the factors after it, and
  `SubwordBeyond.compose` carries a subword found there back across the factor:
  the residual block is `b + N₀ - |A₀|`, exactly as in
  `GreendlingerLanding.landsIn_of_overrun`.

* **It stops inside, keeping at most half.**  Otherwise `|c'| ≤ b < |P''|` and
  `|t'| ≤ 2(k + (b - |c'|))`: the block stops strictly inside what the factor
  keeps, and the factor has lost at least half of its rotation --- `b - |c'|` off
  the front to the block, `k` off the back to its own.  `blockStop_cases` is the
  trichotomy, and this is its third branch.

The first two branches are unconditional and are proved here.  The third is the
one the classical count is about: a factor in it keeps at most half, and the
count says not every factor can.  What a continuation has to supply is a subword
in a factor *after* the one the block stops in --- every letter of those factors
lies beyond the block, so any subword they carry is automatically beyond it, and
`SubwordBeyond.compose` is already the move that carries it back.

Unconditional throughout.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The predicate -/

/-- **A Greendlinger subword beyond a position.**  The word `V` splits with more
than half of a symmetrized relator beginning at or after position `b`. -/
def SubwordBeyond (R : Set (List (α × Bool))) (b : ℕ) (V : List (α × Bool)) :
    Prop :=
  ∃ n : ℕ, b ≤ n ∧ GreendlingerAt R n V

/-- A located subword is a subword beyond its own position. -/
theorem subwordBeyond_of_greendlingerAt {R : Set (List (α × Bool))} {b : ℕ}
    {V : List (α × Bool)} (h : GreendlingerAt R b V) : SubwordBeyond R b V :=
  ⟨b, le_rfl, h⟩

/-- A subword beyond `b` is a subword beyond anything smaller. -/
theorem SubwordBeyond.of_le {R : Set (List (α × Bool))} {b b' : ℕ}
    {V : List (α × Bool)} (h : SubwordBeyond R b V) (hle : b' ≤ b) :
    SubwordBeyond R b' V := by
  obtain ⟨n, hn, hat⟩ := h
  exact ⟨n, by omega, hat⟩

/-- The located conclusion, at exactly the block's length: what
`TailSubwordBeyondBlock` asks for. -/
theorem greendlingerAt_of_subwordBeyond {R : Set (List (α × Bool))} {b : ℕ}
    {V : List (α × Bool)} (h : SubwordBeyond R b V) : GreendlingerAt R b V := by
  obtain ⟨n, hn, hat⟩ := h
  exact hat.mono hn

/-! ## Move one: the factor keeps enough -/

/-- **A factor that keeps more than half of its rotation beyond the block
delivers the subword itself.**  The block eats `b - |c'|` letters off the front
of the rotation and the factor's own block eats at most `k` off the back; if
what is left is more than half, the subword sits at position exactly `b`.

This is `greendlingerAt_of_bounded_cancellation` with its offset spent on the
incoming block rather than on slack, and it is the only producer the search
needs: the other two moves move a subword, they do not make one. -/
theorem subwordBeyond_of_keeps {R : Set (List (α × Bool))}
    {c' t' P'' M'' B'' : List (α × Bool)} {b k : ℕ}
    (ht' : t' ∈ symmetrization R)
    (hsplit : palindrome c' t' = P'' ++ M'')
    (hk : M''.length ≤ (FreeGroup.invRev c').length + k)
    (hb : c'.length ≤ b)
    (hkeep : 2 * (k + (b - c'.length)) < t'.length) :
    SubwordBeyond R b (P'' ++ B'') := by
  refine ⟨c'.length + (b - c'.length), by omega, ?_⟩
  exact greendlingerAt_of_bounded_cancellation ht' hsplit hk hkeep

/-! ## Move two: the block overruns the factor -/

/-- **Carrying a subword back across a cascade step.**  If `V` is
`A₀ ++ V₂.drop N₀` --- one factor's survivor in front of what the rest spells,
with that factor's own block removed --- then a subword of `V₂` beyond the
residual block is a subword of `V` beyond the block.

This is `GreendlingerAt.transport` with the bookkeeping of
`GreendlingerLanding.LandsIn.compose`, and it is what makes the search for a
landing site a *search*: the block is followed one factor at a time and whatever
is found beyond it is carried back. -/
theorem SubwordBeyond.compose {R : Set (List (α × Bool))} {b b' N₀ : ℕ}
    {V V₂ A₀ : List (α × Bool)}
    (h : SubwordBeyond R b' V₂)
    (hV : V = A₀ ++ V₂.drop N₀)
    (hstep : b + N₀ ≤ b' + A₀.length)
    (harrive : N₀ ≤ b') :
    SubwordBeyond R b V := by
  obtain ⟨n, hn, hat⟩ := h
  refine ⟨A₀.length + (n - N₀), by omega, ?_⟩
  rw [hV]
  exact hat.transport A₀ (by omega)

/-- **The overrun case.**  When the block is at least as long as what the factor
in front of it keeps, the residual block is `b + N₀ - |A₀|`. -/
theorem subwordBeyond_of_overrun {R : Set (List (α × Bool))} {b N₀ : ℕ}
    {V V₂ A₀ : List (α × Bool)}
    (hV : V = A₀ ++ V₂.drop N₀)
    (hover : A₀.length ≤ b)
    (h : SubwordBeyond R (b + N₀ - A₀.length) V₂) :
    SubwordBeyond R b V :=
  h.compose hV (by omega) (by omega)

/-- **Everything after the factor the block stops in is beyond the block.**  A
subword carried by the factors past the one the block stops in needs no
arithmetic at all: the block ends inside the survivor `A₀`, so every letter of
what follows lies beyond it. -/
theorem subwordBeyond_of_stops_inside {R : Set (List (α × Bool))} {b N₀ : ℕ}
    {V V₂ A₀ : List (α × Bool)}
    (hV : V = A₀ ++ V₂.drop N₀)
    (hstop : b ≤ A₀.length)
    (h : SubwordBeyond R N₀ V₂) :
    SubwordBeyond R b V :=
  h.compose hV (by omega) le_rfl

/-! ## The trichotomy -/

/-- **What can happen where a block arrives.**  Either the factor keeps more
than half of its rotation beyond the block, or the block outruns everything the
factor keeps, or the block stops strictly inside the survivor and the factor is
left with at most half of its rotation.

`k` is what the factor's own block eats past its trailing conjugator, so
`b - |c'|` and `k` are the two ends the rotation is eaten from.  The three
branches are exactly the three moves above; only the third has no move, and it
is the branch the classical curvature count is about. -/
theorem blockStop_cases {c' : List (α × Bool)}
    (t' P'' : List (α × Bool)) (b k : ℕ) (_ : c'.length ≤ b) :
    2 * (k + (b - c'.length)) < t'.length ∨ P''.length ≤ b ∨
      (b < P''.length ∧ t'.length ≤ 2 * (k + (b - c'.length))) := by
  rcases Nat.lt_or_ge (2 * (k + (b - c'.length))) t'.length with h | h
  · exact Or.inl h
  · rcases le_or_gt P''.length b with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h2, h⟩)

/-! ## The obligation, in the predicate -/

/-- **`TailSubwordBeyondBlock` in the predicate.**  The obligation
`GreendlingerThreeFactor` leaves is exactly a swallow bound together with a
subword beyond the block, so anything that produces `SubwordBeyond` at the
block's length closes the gate. -/
theorem tailSubwordBeyondBlock_of_subwordBeyond [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hsw : ∀ (c t c' t' P' M : List (α × Bool))
      (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
      IsMinimalConjExpr R
        ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g →
      palindrome c t = P' ++ M →
      FreeGroup.invRev M
        <+: (conjEval ((FreeGroup.mk c', t') :: e)).toWord →
      c.length < M.length →
      M.length ≤ c.length + t.length ∧
        SubwordBeyond R M.length
          (conjEval ((FreeGroup.mk c', t') :: e)).toWord) :
    TailSubwordBeyondBlock R := by
  intro c t c' t' P' M e g hmin heq hpre hlong
  obtain ⟨hhigh, hsub⟩ := hsw c t c' t' P' M e g hmin heq hpre hlong
  exact ⟨hhigh, greendlingerAt_of_subwordBeyond hsub⟩

end SmallCancellationRouter
end GroupApproximation
