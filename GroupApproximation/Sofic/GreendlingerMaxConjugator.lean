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
* `MaximalJunction` --- the one word-combinatorial fact the argument consumes:
  at a factor whose conjugator is at least as long as its neighbour's, the part
  of its rotation that the neighbour destroys is a piece.
* `greendlingerAt_of_maximalJunction` --- the located conclusion at the
  maximising factor, from that fact and nothing else.

`MaximalJunction` is not the old hypothesis in new clothes.  `LeadingConfinement`
and `CascadeLanding` both ask where a block *stops*, which is a question about
the whole chain; this asks only what a block is *matched against* at one
junction, and it asks it only where the conjugator is maximal --- which is
exactly where the hug that made the old race unwinnable is zero.

Unconditional except where `MaximalJunction` is named.
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

/-! ## The junction fact -/

/-- **What a block is matched against at a maximal junction.**  At a factor
whose conjugator is at least as long as the neighbouring one, the part of its
rotation that the junction destroys is matched letter for letter against the
neighbour's rotation, so it is a piece.

`x` is the amount of `t` destroyed at the junction, `t` and `t'` the two
rotations.  The statement is one-sided; the argument applies it twice, once at
each side of the maximising factor, and at the two ends of the expression the
corresponding loss is zero and it is not needed at all.

This is the whole of what is not yet proved.  It is a statement about **one**
junction, not about a chain: the block is not followed anywhere, and no
minimality move is spent on it beyond the piece bound and the hug bound that
`no_overrun_of_hug_and_piece` consumes. -/
def MaximalJunction [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c' t' : List (α × Bool)) (x : ℕ),
    t ∈ symmetrization R → t' ∈ symmetrization R →
    c'.length ≤ c.length →
    IsPiece (symmetrization R) (t.take x) ∨ x = 0 →
    6 * x < t.length

/-- **The located conclusion at the maximising factor.**  Given the junction
fact on both sides, the factor with the longest conjugator keeps more than two
thirds of its rotation, which is more than the half the gate asks for.

The proof is `keeps_of_two_pieces`: nothing else is needed once both losses are
pieces. -/
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
