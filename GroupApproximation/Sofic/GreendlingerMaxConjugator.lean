import GroupApproximation.Sofic.GreendlingerBeyond

/-!
# The factor with the longest conjugator

Every route so far has followed the *leading* factor and asked where its block
stops.  That is the wrong factor to follow.  The right one is the factor whose
**conjugator is longest**, and at that factor both of the losses are pieces
outright --- no hugs, no reroutes, no race between five twelfths and seven
twelfths.

## Why the longest conjugator

Write the minimal expression as `∏ᵢ palindrome cᵢ tᵢ`, put `dᵢ = |cᵢ|` and
`Tᵢ = |tᵢ|`, and let `m` maximise `d`.  The free reduction of the concatenation
matches destroyed letters in a **nested** pattern, and no matched pair lies
inside one palindrome (each is reduced), so the letters destroyed off the front
of `palindrome c_m t_m` are matched, innermost first, against the reversed tail
of what stands to the left --- and that tail begins with `invRev c_{m-1}`,
`d_{m-1}` letters of conjugator, followed by `t_{m-1}`.

Because `d_{m-1} ≤ d_m`, the conjugator `c_m` covers all of `invRev c_{m-1}`
before any letter of `t_m` is reached.  **So every destroyed letter of `t_m` is
matched against a letter of `t_{m-1}`**: the eaten part is a common subword of
two symmetrized relators, i.e. a piece, and `C'(1/6)` bounds it by a sixth.  The
same argument on the right, using `d_{m+1} ≤ d_m`, bounds the loss there.  Two
sixths gone, so `t_m` keeps more than two thirds of itself --- and the surviving
stretch is contiguous, hence an infix of the reduced word.

At the ends there is nothing to lose: `λ = 0` at `m = 1` and `ρ = 0` at `m = n`.

The one place the reading could fail is if the eaten part ran past `t_{m-1}`
altogether; `no_overrun_of_hug_and_piece` rules that out, because the part of
`c_m` running along `t_{m-1}` is a hug (at most half of `t_{m-1}`) and the part
of `t_m` running along it is a piece (under a sixth), and a half and a sixth do
not cover a whole.

## What this file proves

The arithmetic of that argument, unconditionally, and the selection of `m`:

* `keeps_of_two_pieces` --- two sixths leave more than a half (in fact more than
  two thirds).
* `no_overrun_of_hug_and_piece` --- a hug and a piece cannot cover a rotation.
* `exists_max_index` --- a maximiser exists, and it dominates both neighbours.
* `not_overrun_into_conjugator` --- **an overrun never lands in a conjugator**,
  so the hug between factors two apart --- the configuration no reroute identity
  reaches --- cannot occur at a maximiser.
* `not_second_overrun` --- **a block overruns at most one factor**, so each loss
  is at most two pieces.
* `conjEval_block_ne_one` --- **no contiguous block of factors spells `1`**, so
  no run of whole factors cancels among itself.  This generalises
  `conj_ne_inv_of_minimal` from two factors to any number, and it is what says
  the nested matching cannot skip whole factors: the partner of the letter next
  to a chunk is the letter next to it.
* `MaximalJunction` --- **DEMOTED: vacuous.**  It was meant to be the one
  word-combinatorial fact the argument consumes, and it is not; see the section
  where it is defined.
* `greendlingerAt_of_maximalJunction` --- the located conclusion at the
  maximising factor.  **Unconditional**: it takes the numeric bound as a
  hypothesis and never mentions `MaximalJunction`.

## The demotion, and what it costs

An earlier version of this header claimed `MaximalJunction` was "the one
word-combinatorial fact the argument consumes" and that the file was
"unconditional except where `MaximalJunction` is named".  Both are false.

The predicate takes `IsPiece (symmetrization R) (t.take x)` as a *hypothesis*
and concludes `6 * x < t.length`, which the metric condition already gives for
any piece whatever: `t.take x` is a prefix of `t` unconditionally, so
`six_mul_length_lt_of_isPiece` applies to it directly, and the `x = 0` branch
needs only `t ≠ []`.  So `MaximalJunction R` is a **theorem** given `C'(1/6)`
and `∀ r ∈ R, r ≠ []`, and discharging it closes nothing.

The tell is in the binder list: neither the hypothesis nor the conclusion
mentions `c`, `c'` or `t'` --- both speak only of `t` and `x`.  The conjugator
domination `c'.length ≤ c.length`, which is the entire content of the word
"maximal", is inert, as is the neighbour's membership `t' ∈ symmetrization R`.
The predicate says nothing about a junction at all.

The sharp twin `GreendlingerSharpTwins.MaximalJunctionSharp` inherited the
defect verbatim and is demoted there too;
`GreendlingerLandingProd.maximalJunctionSharp_of_metric` is the written proof of
its vacuity, and the same two branches settle this one at `1/6`.

**What the statement would have to say.**  The content the maximal-conjugator
argument needs is word-level and comes *before* the numeric step: that at such a
junction the destroyed part **is** `t.take x` and **is** a piece, as a
consequence of the conjugator domination.  That is what the prose at the top of
this file argues informally and what the predicate skips, and it is stated
nowhere in the lane.  It is not restated here either: writing it correctly needs
the junction configuration --- which palindrome, which cancellation, what
"destroyed" names --- and inventing a predicate without that data is exactly the
failure this demotion records.

Everything else in this file stands: the arithmetic and the selection of `m` are
unconditional, and were never routed through the predicate.  The route itself is
not the live one --- the lane runs through `DeepArcSourceSharp` and the (β)
side.  `MaximalJunction` is kept rather than deleted so the trap stays on the
record.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The arithmetic -/

/-- **Two sixths leave two thirds.**  A rotation eaten by a piece at each end
keeps more than two thirds of itself, and in particular more than half. -/
theorem keeps_of_two_pieces {x y T : ℕ} (hx : 6 * x < T) (hy : 6 * y < T) :
    2 * (x + y) < T := by omega

/-- **A hug and a piece do not cover a rotation.**  What a conjugator eats of the
rotation it runs along is at most half of it, and what a rotation eats of another
is under a sixth; a half and a sixth leave a third standing.

This is what stops the reading of the junction from running off the end of the
neighbour's rotation, and it is the only inequality in the argument that is not
immediate. -/
theorem no_overrun_of_hug_and_piece {h p T : ℕ} (hhug : 2 * h ≤ T)
    (hpiece : 6 * p < T) (hcover : T ≤ h + p) : False := by omega

/-- The eaten part of a rotation, at a junction where the conjugator is maximal,
is bounded by a sixth on each side, so the survivor is a genuine infix and more
than half. -/
theorem survivor_gt_half {x y T : ℕ} (hx : 6 * x < T) (hy : 6 * y < T)
    (hT : 0 < T) : T < 2 * (T - x - y) := by omega

/-- **Three pieces still leave a half.**  When the block overruns one factor the
left loss is two pieces rather than one; a sixth each on the left and a sixth on
the right still lose less than a half in total.

This is why an overrun that lands among *relator* letters costs nothing: the
budget is three sixths against one half, and three sixths is exactly a half only
in the limit, which the strict piece bound never reaches. -/
theorem keeps_of_three_pieces {x₁ x₂ y T : ℕ}
    (h1 : 6 * x₁ < T) (h2 : 6 * x₂ < T) (hy : 6 * y < T) :
    2 * (x₁ + x₂ + y) < T := by omega

/-- **An overrun never lands in a conjugator.**  Suppose the block from the
maximising factor eats the neighbouring factor's rotation whole:
`T ≤ g + h + p`, where `h` is the hug the maximiser's own conjugator contributes,
`p` the piece it meets, and `g` what the factor on the far side contributes.

If the overrun landed among conjugator letters, that far contribution would be a
*strict* hug inside a conjugator no longer than the maximiser's, giving `g < h`.
But the meet bound `2h + p ≤ T` (`overhang_le_of_minimal_reroute_meet`) then
gives `T ≤ g + h + p < 2h + p ≤ T`.

So the overrun always lands among **relator** letters, where it is another
piece.  This is the configuration that blocked every earlier route --- a hug
between factors two apart, which no reroute identity reaches --- and it simply
cannot occur at a maximiser.  Nothing about the *choice* of maximiser is used,
only that no conjugator is longer. -/
theorem not_overrun_into_conjugator {g h p T : ℕ}
    (hcover : T ≤ g + h + p) (hmeet : 2 * h + p ≤ T) (hshort : g < h) :
    False := by omega

/-- **An overrun never passes a second factor.**  To pass the factor it landed
in, the block would have to eat everything that factor has left; what it eats is
a piece, under a sixth, so the factor's rotation must already be more than five
sixths gone --- `5T < 6(p + L)` with `p` the piece the block eats and `L` what
the factor lost at its own far junction.

But `L` is a hug and a piece, so `2·hug + piece ≤ T` and `6·piece < T` bound it
by seven twelfths, and a sixth and seven twelfths make three quarters, not five
sixths.

So a block overruns **at most one factor**, and the loss it inflicts on the
maximiser's rotation is at most two pieces. -/
theorem not_second_overrun {p L hug pc T : ℕ}
    (hpass : 5 * T < 6 * (p + L)) (hp : 6 * p < T)
    (hL : L = hug + pc) (hmeet : 2 * hug + pc ≤ T) (hpc : 6 * pc < T) :
    False := by omega

/-! ## Choosing the factor -/

/-- **A maximiser exists.**  Among `f 0, …, f n` some index dominates all of
them; the factor it names is the one the argument follows. -/
theorem exists_max_index (f : ℕ → ℕ) :
    ∀ n : ℕ, ∃ m ≤ n, ∀ k ≤ n, f k ≤ f m := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro k hk
      rw [Nat.le_zero.mp hk]
  | succ n ih =>
      obtain ⟨m, hmn, hmax⟩ := ih
      rcases le_or_gt (f (n + 1)) (f m) with h | h
      · refine ⟨m, by omega, ?_⟩
        intro k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hk'
        · exact h
        · exact hmax k (by omega)
      · refine ⟨n + 1, le_rfl, ?_⟩
        intro k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hk'
        · exact le_rfl
        · exact le_trans (hmax k (by omega)) h.le

/-- The maximiser dominates both of its neighbours, which is all the argument
uses: the hug into its own rotation is zero on both sides. -/
theorem max_index_neighbours {f : ℕ → ℕ} {m n : ℕ} (hm : m ≤ n)
    (hmax : ∀ k ≤ n, f k ≤ f m) :
    (∀ k, k < m → f k ≤ f m) ∧ (m < n → f (m + 1) ≤ f m) := by
  refine ⟨fun k hk => hmax k (by omega), fun hlt => hmax (m + 1) (by omega)⟩

/-- **The least maximiser is safe on the left.**  Nothing before it attains the
maximum, so `eq_max_of_overrun_into_conjugator` cannot be satisfied there. -/
theorem least_max_left_safe {f : ℕ → ℕ} {m n : ℕ}
    (_hmax : ∀ k ≤ n, f k ≤ f m)
    (hleast : ∀ k < m, f k < f m) :
    ∀ j, j + 2 = m → f j < f m := by
  intro j hj
  exact hleast j (by omega)

/-- The least maximiser exists: take the least index attaining the maximum. -/
theorem exists_least_max (f : ℕ → ℕ) (n : ℕ) :
    ∃ m ≤ n, (∀ k ≤ n, f k ≤ f m) ∧ ∀ k < m, f k < f m := by
  classical
  obtain ⟨M, hMn, hMmax⟩ := exists_max_index f n
  have hex : ∃ m, m ≤ n ∧ f m = f M := ⟨M, hMn, rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_⟩
  · intro k hk
    rw [(Nat.find_spec hex).2]
    exact hMmax k hk
  · intro k hk
    have hne : ¬ (k ≤ n ∧ f k = f M) := Nat.find_min hex hk
    have hkn : k ≤ n := by
      have := (Nat.find_spec hex).1
      omega
    have : f k ≠ f M := fun h => hne ⟨hkn, h⟩
    have hle := hMmax k hkn
    rw [(Nat.find_spec hex).2]
    omega

/-! ## No block of factors cancels among itself -/

/-- **No contiguous block of factors spells the identity.**  If a run of factors
in the middle of a minimal expression multiplied to `1`, deleting the whole run
would spell the same element with fewer factors.

`GreendlingerThreeFactor.conj_ne_inv_of_minimal` is the two-factor case (one
factor inverse to a later one).  This is the general one, and it is what the
matching argument needs: a **self-matched block of whole factors** is exactly a
run whose concatenation freely reduces to nothing, hence whose product is `1`.
So the nested matching of a destroyed run cannot skip over whole factors, and
the partner of the letter next to a surviving chunk is the letter next to it.

Unconditional, and it uses only minimality of the factor count. -/
theorem conjEval_block_ne_one [DecidableEq α] {R : Set (List (α × Bool))}
    {e₁ e₂ e₃ : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R (e₁ ++ (e₂ ++ e₃)) g) (hne : e₂ ≠ []) :
    conjEval e₂ ≠ 1 := by
  intro hone
  obtain ⟨hv, he, hlen, -⟩ := hmin
  have hv₁ : ConjValid R e₁ := fun z hz => hv z (List.mem_append_left _ hz)
  have hv₂ : ConjValid R e₃ := fun z hz =>
    hv z (List.mem_append_right _ (List.mem_append_right _ hz))
  have heval : conjEval (e₁ ++ e₃) = g := by
    rw [conjEval_append, ← he, conjEval_append, conjEval_append, hone, one_mul]
  have hb := hlen (e₁ ++ e₃) (conjValid_append hv₁ hv₂) heval
  simp only [List.length_append] at hb
  have h₂ : 0 < e₂.length := List.length_pos_iff.mpr hne
  omega

/-- **A factor is never destroyed against factors it is not next to.**  The
form the matching argument uses: a run of whole factors between two surviving
chunks cannot cancel away, so the destroyed letters adjacent to a chunk are
matched against the factor immediately beside it. -/
theorem conjEval_middle_ne_one [DecidableEq α] {R : Set (List (α × Bool))}
    {x : FreeGroup α × List (α × Bool)}
    {e₁ e₂ e₃ : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R (e₁ ++ ((x :: e₂) ++ e₃)) g) :
    conjEval (x :: e₂) ≠ 1 :=
  conjEval_block_ne_one hmin (List.cons_ne_nil x e₂)

/-! ## The junction fact -/

/-- **DEMOTED --- this predicate assumes its own content and is a theorem.**

The intent was: at a factor whose conjugator is at least as long as the
neighbouring one, the part of its rotation that the junction destroys is matched
letter for letter against the neighbour's rotation, so it is a piece.  The
statement below does not say that.  It *takes* `IsPiece (symmetrization R)
(t.take x)` as a hypothesis and concludes a numeric bound the metric condition
already gives for any piece: `t.take x <+: t` holds unconditionally, so
`six_mul_length_lt_of_isPiece` applies to it with no junction geometry, and the
`x = 0` branch needs only `t ≠ []`.  Given `C'(1/6)` and nonempty relators this
is a theorem, so it is not "the whole of what is not yet proved" --- it is not
open at all, and discharging it would close nothing.

Neither the hypothesis nor the conclusion mentions `c`, `c'` or `t'`: both speak
only of `t` and `x`.  So the domination `c'.length ≤ c.length` --- the whole
content of "maximal" --- and the membership `t' ∈ symmetrization R` are inert,
and the predicate is not about a junction.

`GreendlingerSharpTwins.MaximalJunctionSharp` is the sharp twin, demoted the
same way, and `GreendlingerLandingProd.maximalJunctionSharp_of_metric` is the
written proof of the vacuity.  The module header records what the missing
word-level statement would have to assert.

Kept rather than deleted so the trap stays on the record. -/
def MaximalJunction [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c' t' : List (α × Bool)) (x : ℕ),
    t ∈ symmetrization R → t' ∈ symmetrization R →
    c'.length ≤ c.length →
    IsPiece (symmetrization R) (t.take x) ∨ x = 0 →
    6 * x < t.length

/-- **The located conclusion at the maximising factor.**  A rotation losing at
most `x` at one end keeps more than two thirds of itself, which is more than the
half the gate asks for.  The proof is `keeps_of_two_pieces`: nothing else is
needed once both losses are pieces.

This is **unconditional**, and it is worth being exact about why.  It does not
mention `MaximalJunction`, and never did: it takes the numeric bound `hx` as a
hypothesis, and the demoted predicate would only have supplied that same bound.
An earlier docstring said "given the junction fact on both sides", which read as
though the theorem were conditional on the predicate; it is not. -/
theorem greendlingerAt_of_maximalJunction {R : Set (List (α × Bool))}
    {c t P' M B' : List (α × Bool)} {x j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hM : M.length ≤ (FreeGroup.invRev c).length + x)
    (hx : 6 * x < t.length) (hj : 6 * j < t.length) :
    GreendlingerAt R (c.length + j) (P' ++ B') :=
  greendlingerAt_of_bounded_cancellation ht heq hM (by omega)

end SmallCancellationRouter
end GroupApproximation
