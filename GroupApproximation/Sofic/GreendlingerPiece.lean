import GroupApproximation.Sofic.GreendlingerDescent

/-!
# Pieces, in the arithmetic the descent speaks

`GreendlingerDescent` reduced the descent to a budget: a cancellation reaching
`k` letters past the conjugator leaves `t.take (|t| - k)`, and `2k < |t|` already
gives the Greendlinger conclusion.  The `C'(1/6)` hypothesis is what supplies
`2k < |t|`, but it speaks in `ℚ` about *pieces*, and the descent speaks in `ℕ`
about eaten suffixes.  This file is the translation.

Three short bridges:

* `invRev_prefix_of_suffix` -- the formal inverse turns suffixes into prefixes,
  because `invRev` is an anti-homomorphism.  So the suffix of a rotation that a
  cancellation eats has its inverse a *prefix* of a rotation, and
  `symmetrization` is closed under `invRev`, so a prefix of a symmetrized
  relator.
* `isPiece_of_prefix_two` -- being a common prefix of two *distinct* symmetrized
  relators is what `IsPiece` says, named so the descent can cite it.
* `six_mul_length_lt_of_isPiece` -- `C'(1/6)` in `ℕ`: a piece prefixing a
  symmetrized relator `w` satisfies `6|p| < |w|`.  Clearing the denominator once,
  here, keeps every downstream step in `omega`'s reach.

`greendlinger_of_piece_cancellation` then closes the descent's second case: if
the overlap the cancellation eats out of the rotation is a piece, the conclusion
follows, because `6k < |t|` is far more than the `2k < |t|` the budget needs.

## What is and is not assumed

The `C'(1/6)` hypothesis is the gate's own hypothesis about the relator family,
not an imported theorem.  The `IsPiece` hypothesis of the last statement is a
concrete combinatorial property of the particular words involved -- it is the
step the minimality of the expression has to supply, and it is stated as a
hypothesis here precisely so that it is visible as the one thing still owed,
rather than hidden.

Unconditional otherwise.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Suffixes become prefixes under the formal inverse -/

/-- `invRev` is an anti-homomorphism, so it turns suffixes into prefixes. -/
theorem invRev_prefix_of_suffix {M L : List (α × Bool)} (h : M <:+ L) :
    FreeGroup.invRev M <+: FreeGroup.invRev L := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨FreeGroup.invRev d, FreeGroup.invRev_append.symm⟩

/-- The suffix of a symmetrized relator that a cancellation eats has its formal
inverse a prefix of a symmetrized relator. -/
theorem exists_prefix_symmetrization_of_suffix {R : Set (List (α × Bool))}
    {M t : List (α × Bool)} (ht : t ∈ symmetrization R) (h : M <:+ t) :
    ∃ s ∈ symmetrization R, FreeGroup.invRev M <+: s :=
  ⟨FreeGroup.invRev t, invRev_mem_symmetrization ht,
    invRev_prefix_of_suffix h⟩

/-! ## Pieces -/

/-- A common prefix of two distinct symmetrized relators is a piece; this is
`IsPiece` unfolded, named for citation. -/
theorem isPiece_of_prefix_two {S : Set (List (α × Bool))}
    {p s₁ s₂ : List (α × Bool)} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) (hne : s₁ ≠ s₂)
    (hp₁ : p <+: s₁) (hp₂ : p <+: s₂) : IsPiece S p :=
  ⟨s₁, h₁, s₂, h₂, hne, hp₁, hp₂⟩

/-- **`C'(1/6)` in `ℕ`.**  Clearing the denominator once keeps every downstream
step inside `omega`'s reach. -/
theorem six_mul_length_lt_of_isPiece {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {p w : List (α × Bool)} (hp : IsPiece (symmetrization R) p)
    (hw : w ∈ symmetrization R) (hpre : p <+: w) :
    6 * p.length < w.length := by
  have h := hmetric p hp w hw hpre
  have h6 : (6 : ℚ) * (p.length : ℚ) < (w.length : ℚ) := by linarith
  exact_mod_cast h6

/-- The same, read on the eaten suffix of a rotation. -/
theorem six_mul_length_lt_of_eaten {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6)) {M t : List (α × Bool)}
    (ht : t ∈ symmetrization R) (hsuf : M <:+ t)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev M)) :
    6 * M.length < t.length := by
  have h := six_mul_length_lt_of_isPiece hmetric hpiece
    (invRev_mem_symmetrization ht) (invRev_prefix_of_suffix hsuf)
  rwa [FreeGroup.invRev_length, FreeGroup.invRev_length] at h

/-! ## The descent's second case -/

/-- **The descent's second case.**  If the overlap the cancellation eats out of
the rotation is a piece, the Greendlinger conclusion follows: `C'(1/6)` gives
`6k < |t|`, and the budget of `GreendlingerDescent` needs only `2k < |t|`.

The `IsPiece` hypothesis is the one thing still owed by the descent: it is what
minimality of the expression has to supply, and it is a hypothesis here so that
it stays visible rather than hidden. -/
theorem greendlinger_of_piece_cancellation {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t P' M B' E : List (α × Bool)}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧ s.length < 2 * u.length := by
  have h6 := six_mul_length_lt_of_eaten hmetric ht hE hpiece
  exact greendlinger_of_bounded_cancellation hRne ht heq hlen (by omega)

end SmallCancellationRouter
end GroupApproximation
