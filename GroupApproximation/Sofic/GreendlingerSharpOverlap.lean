import GroupApproximation.Sofic.GreendlingerSharpMinimal
import GroupApproximation.Sofic.GreendlingerSharpRegime

/-!
# The overlap layer at an arbitrary constant, and the leftovers around it

`GreendlingerOverlap` pays the piece hypothesis the descent owed: an overlap
eaten out of one symmetrized relator and landing in another is a piece unless
the two coincide, and the coincidence collapses the expression.  Almost all of
that file is `λ`-neutral --- it is anti-homomorphism bookkeeping about `invRev`,
rotations and prefixes, and nothing in it reads a small-cancellation constant.
What does read one is the last two statements, `greendlinger_of_distinct_overlap`
and `greendlinger_of_two_palindromes`, both stated at `C'(1/6)` and both
finishing in the half form `|s| < 2|u|`.  This file states them at an arbitrary
`λ`, together with the three statements in the neighbouring layers that were
left without twins.

## What is `λ`-neutral, and therefore has no twin

Recorded here because a verdict of "needs no twin" is worth as much as a twin,
and re-deriving it costs a reading of each file.

* **`GreendlingerConjugation` in its entirety.**  One-letter conjugation of a
  cyclically reduced word --- `mk_conj_head`, `mk_conj_last`,
  `not_cancel_head_and_last`, `isReduced_conj_letter`, `conj_letter_cases` ---
  names no constant and no piece.  It is free-group combinatorics feeding the
  palindromic normal form.
* **The whole splitting half of `GreendlingerOverlap`**:
  `suffix_split_of_length_le`, `eaten_split`, `eaten_suffix_of_le`,
  `invRev_eaten_block`, `prefix_rotate_of_append_prefix`,
  `exists_split_of_overlap_prefix`, `isPiece_of_overlap`, `mk_rotate_conj`,
  both `mk_palindrome_mul_eq_one_of_coincidence` forms, and
  `exists_overlap_of_cancellation`.  Each is quoted unchanged by the sharp lane
  --- `GreendlingerSharpLandingAux.greendlingerAtSharp_of_overlap` calls three
  of them by name.
* **`GreendlingerCoincidence` apart from its last theorem.**
  `invRev_ne_rotate_of_minimal` and `exists_effectiveConjugator` spend
  minimality, not `C'(λ)`.
* **`GreendlingerDeepestMatch` §1**: `eaten_prefix_orientation` and
  `invRev_eaten_drop` are positional.
* **`GreendlingerInduction` §1**: `conjValid_append`, `IsMinimalConjExpr.tail`
  and `IsMinimalConjExpr.leadingPair` are hereditary minimality and read no
  bound.
* **`GreendlingerFreeGate` in its entirety.**  It is already stated at a
  general `λ` --- `SharpGreendlingerGate` quantifies over the constant --- and
  the places it writes `1/6` are deliberate *evaluations* of the sharp gate at
  the value where `1 - 3λ = 1/2`, not artefacts of clearing a denominator.

## What moves, and what it costs

The offset.  `GreendlingerOverlap`'s two producers conclude in the unlocated
shape --- some subword of `P' ++ B'` beats half a relator --- so their sharp
twins are the located producers read at offset `0`, and an offset of `0` is
admissible only when `0 < λ`, since the sharp located predicate measures the
offset against `λ·|t|`.  The `λ`-free file pays nothing there, because its
offset condition at `j = 0` is `6·0 < |t|`.  That is the same `0 < λ` the rest
of the sharp lane spends, and `GreendlingerSharpTwins.lam_pos_of_metric` derives
it from the metric condition on any nondegenerate family, so no consumer has to
supply it.

`λ ≤ 1/6` is inherited from
`GreendlingerSharpTwins.greendlingerAtSharp_of_bounded_cancellation` and is used
only to know that the losses stay inside the rotation they are measured against.

## The one place the two towers do not meet

`greendlingerConclusionSharp_of_three_factor` below carries a hypothesis its
`λ`-free counterpart does not: `TwoFactorRegime`.  The reason is upstream.
`GreendlingerRegime.greendlinger_of_le_two_factors` *derives* the regime inside
the descent, where it has the minimal expression in hand, by calling
`swallow_bound_of_minimal` and `swallow_bound_of_minimal'`; the sharp two-factor
theorem `GreendlingerSharpMinimal.greendlingerSharp_of_isMinimalConjProduct_two`
instead takes the regime as a hypothesis.  Both sharp swallow bounds exist ---
`GreendlingerSharpRegime.swallow_bound_of_minimal_sharp` and
`swallow_bound_of_minimal_sharp'`, at `λ ≤ 1/3` --- so the derivation is
available in principle, but performing it means replaying the descent
decomposition, which belongs in the regime file and not here.  Until that is
done the sharp three-factor reduction is strictly weaker than the `λ`-free one,
and the hypothesis is named rather than hidden.

Nothing here is new mathematics; it is the `λ = 1/6` evaluation undone.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The metric condition, named -/

/-- **`C'(λ)` on a piece, named.**  The `λ`-twin of
`GreendlingerPiece.six_mul_length_lt_of_isPiece`.

The `λ`-free version clears the denominator once, so that everything downstream
stays inside `omega`'s reach; at a general `λ` there is nothing to clear and the
statement is the metric condition itself, reassociated for citation.  It is
recorded because many twins want the bound in this shape and none of them
should have to unfold `MetricSmallCancellation` to get it.

`GreendlingerSharpTwins.length_lt_of_eaten` is the same bound read on an eaten
suffix, which is the form the descent produces. -/
theorem length_lt_of_isPiece {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {p w : List (α × Bool)} (hp : IsPiece (symmetrization R) p)
    (hw : w ∈ symmetrization R) (hpre : p <+: w) :
    (p.length : ℚ) < lam * (w.length : ℚ) :=
  hmetric p hp w hw hpre

/-! ## 2.  The overlap producers, in the unlocated shape -/

/-- **The descent's second case at an arbitrary constant.**  The `λ`-twin of
`GreendlingerPiece.greendlinger_of_piece_cancellation`.

If the overlap the cancellation eats out of the rotation is a piece, the sharp
conclusion follows: `C'(λ)` bounds the overlap by `λ|t|`, which is one piece out
of the budget of three that `(1 - 3λ)` allows, and the remaining two are spent
on nothing --- the subword is taken at offset `0`.

The `IsPiece` hypothesis is the same thing the `λ`-free file leaves visible: it
is what minimality of the expression has to supply, and it is discharged one
layer up by `isPiece_of_overlap`, which reads no constant. -/
theorem greendlingerSharp_of_piece_cancellation {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t P' M B' E : List (α × Bool)}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  have htpos : 0 < t.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
  exact greendlingerSharp_of_greendlingerAtSharp
    (greendlingerAtSharp_of_two_pieces (B' := B') hlam ht heq hlen
      (length_lt_of_eaten hmetric ht hE hpiece)
      (cast_zero_lt_lam_mul hlam0 htpos))

/-- **The descent's second case with the piece hypothesis discharged, at an
arbitrary constant.**  The `λ`-twin of
`GreendlingerOverlap.greendlinger_of_distinct_overlap`.

What stands in place of the piece hypothesis is the distinctness of two words,
and `isPiece_of_overlap` --- which names no constant --- turns it into the
piece.  Only the bound the piece is then read against moves. -/
theorem greendlingerSharp_of_distinct_overlap {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t t' P' M B' E : List (α × Bool)} {k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpre : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) :=
  greendlingerSharp_of_piece_cancellation hlam0 hlam hRne hmetric ht heq hE hlen
    (isPiece_of_overlap ht ht' hE hpre hne)

/-- **The two-factor descent at an arbitrary constant, in the regime where the
leading conjugator is the longer.**  The `λ`-twin of
`GreendlingerOverlap.greendlinger_of_two_palindromes`, and the missing partner
of `GreendlingerSharpMinimal.greendlingerSharp_of_two_palindromes_mirror`.

Either the cancellation stays inside the trailing conjugator and the whole
leading rotation survives, or it eats an overlap, and that overlap is a piece
--- because were it not, the two factors would spell mutually inverse elements,
which `hcoin` forbids and which minimality of the expression supplies.

The geometry is `λ`-free and is not replayed: the located producer
`GreendlingerSharpLandingAux.greendlingerAtSharp_of_overlap` already performs
the case split, and this is that producer read at offset `0`, which is what
`0 < λ` pays for.  The `λ`-free version needs no such hypothesis, because at
offset `0` its condition `6·0 < |t|` is nonemptiness alone. -/
theorem greendlingerSharp_of_two_palindromes {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M B' : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hpre : FreeGroup.invRev M <+: palindrome c' t')
    (hhigh : M.length ≤ (FreeGroup.invRev c).length + t.length)
    (hle : c'.length ≤ c.length)
    (hfit : c.length - c'.length + M.length ≤ c.length + t'.length)
    (hcoin : FreeGroup.mk (palindrome c t)
      * FreeGroup.mk (palindrome c' t') ≠ 1) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  have htpos : 0 < t.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
  exact greendlingerSharp_of_greendlingerAtSharp
    (greendlingerAtSharp_of_overlap (B' := B') hlam hmetric ht ht' heq hpre
      hhigh hle hfit hcoin (cast_zero_lt_lam_mul hlam0 htpos))

/-! ## 3.  The one-relator base, keyed to the family -/

/-- **The sharp one-relator conclusion, keyed to a relator of the family.**  The
`λ`-twin of `GreendlingerOneRelator.greendlinger_of_isConj_relator`: the same
one line, over `GreendlingerSharpMinimal.greendlingerSharp_of_isConj` instead of
its `λ`-free version. -/
theorem greendlingerSharp_of_isConj_relator [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {r : List (α × Bool)} (hr : r ∈ R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hconj : IsConj (FreeGroup.mk r) (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧
        (1 - 3 * lam) * (t.length : ℚ) < (u.length : ℚ) :=
  greendlingerSharp_of_isConj hlam0 hR hRne (subset_symmetrization R hr) hw
    hconj

/-- **The same, keyed to an inverted relator.**  The `λ`-twin of
`GreendlingerOneRelator.greendlinger_of_isConj_inv`, and the other half of what
`exists_isConj_of_mem_symmetrization` produces.  The formal inverse is carried
into the symmetrization by `invRev_mem_symmetrization`, which reads no
constant. -/
theorem greendlingerSharp_of_isConj_inv [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {r : List (α × Bool)} (hr : r ∈ R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hconj : IsConj (FreeGroup.mk r)⁻¹ (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧
        (1 - 3 * lam) * (t.length : ℚ) < (u.length : ℚ) := by
  refine greendlingerSharp_of_isConj hlam0 hR hRne
    (invRev_mem_symmetrization (subset_symmetrization R hr)) hw ?_
  rwa [FreeGroup.inv_mk] at hconj

/-- **The length form of the one-relator base, at an arbitrary constant.**  The
`λ`-twin of `GreendlingerOneRelator.norm_bound_of_isConj`: a single conjugate of
a symmetrized relator is longer than `(1 - 3λ)` of some symmetrized relator.

This is what `GreendlingerFreeGate.norm_bound_of_sharpGate` concludes from the
gate, obtained without the gate whenever the element is a single conjugate.  The
`λ`-free version finishes in `ℕ` with `omega`; here the subword bound has to be
cast, and nothing else changes. -/
theorem norm_bound_of_isConj_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {s : List (α × Bool)} (hs : s ∈ symmetrization R)
    {g : FreeGroup α} (hconj : IsConj (FreeGroup.mk s) g) :
    ∃ t ∈ symmetrization R,
      (1 - 3 * lam) * (t.length : ℚ) < (FreeGroup.norm g : ℚ) := by
  have hmk : FreeGroup.mk g.toWord = g := FreeGroup.mk_toWord
  obtain ⟨t, ht, u, huinf, -, hlt⟩ :=
    greendlingerSharp_of_isConj hlam0 hR hRne hs FreeGroup.isReduced_toWord
      (by rwa [hmk])
  refine ⟨t, ht, ?_⟩
  have h1 : u.length ≤ g.toWord.length := huinf.sublist.length_le
  have h2 : FreeGroup.norm g = g.toWord.length := rfl
  have h3 : (u.length : ℚ) ≤ (FreeGroup.norm g : ℚ) := by
    rw [h2]
    exact_mod_cast h1
  linarith

/-! ## 4.  The induction layer

`GreendlingerInduction` states two reductions of the gate to what is left of the
descent.  Both are twinned here; the first carries a warning and the second
carries a hypothesis, and both are explained where they are stated. -/

/-- **The strengthened gate at an arbitrary constant.**  The `λ`-twin of
`GreendlingerInduction.GreendlingerTwoPiece`, over
`GreendlingerSharpRegime.TwoPieceConclusionSharp`.

**The warning attached to the `λ`-free predicate carries over verbatim, and
stating it sharply does not repair it.**  Greendlinger's lemma gives two regions
each meeting the boundary in a stretch consecutive along *its own* boundary;
`TwoPieceConclusionSharp` asks for two subwords consecutive along `w`, and when
the second region's arc wraps past the basepoint those differ.
`GreendlingerTwoPieceRegime` carries the witness.  What is stated below is still
correct --- the strengthened statement does imply the sharp gate --- it is
simply not reachable, so do not spend the induction on it. -/
def GreendlingerTwoPieceSharp (R : Set (List (α × Bool))) (lam : ℚ) : Prop :=
  ∀ w : List (α × Bool), FreeGroup.IsReduced w → ∀ n : ℕ, 2 ≤ n →
    IsMinimalConjProduct R n (FreeGroup.mk w) → TwoPieceConclusionSharp R lam w

/-- **The strengthened gate implies the sharp gate.**  The `λ`-twin of
`GreendlingerInduction.greendlingerConclusion_of_greendlingerTwoPiece`.

The base cases are already closed at the sharp constant: none is impossible for
a nonempty reduced word --- that clause is `λ`-free --- and one is
`GreendlingerSharpMinimal.greendlingerSharp_of_isConjProduct_one`, which is
where `0 < λ` is spent.  The metric condition is not needed, exactly as in the
`λ`-free version: the strengthened hypothesis has already done the work
`C'(λ)` would have done. -/
theorem greendlingerConclusionSharp_of_greendlingerTwoPieceSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (h : GreendlingerTwoPieceSharp R lam) : GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨n, hmin⟩ :=
    exists_isMinimalConjProduct_of_mem_normalClosure R (FreeGroup.mk w) hmem
  rcases n with _ | _ | n
  · exact absurd hmin.1 (not_isConjProduct_zero hw hwne)
  · exact greendlingerSharp_of_isConjProduct_one hlam0 hR hRne hw hmin.1
  · exact greendlingerSharp_of_twoPieceConclusionSharp
      (h w hw (n + 1 + 1) (by omega) hmin)

/-- **What is still open, sharply.**  The `λ`-twin of
`GreendlingerInduction.greendlingerConclusion_of_three_factor`: the sharp gate
follows from the case of three or more factors alone.

`hregime` is the one hypothesis the `λ`-free statement does not carry, and it is
not an artefact of the constant.  `GreendlingerRegime.greendlinger_of_le_two_factors`
derives `TwoFactorRegime` inside the descent, where the minimal expression is in
hand, from `swallow_bound_of_minimal` and `swallow_bound_of_minimal'`; the sharp
two-factor theorem takes it as a hypothesis instead.  The sharp swallow bounds
that would discharge it exist ---
`GreendlingerSharpRegime.swallow_bound_of_minimal_sharp` and
`swallow_bound_of_minimal_sharp'`, at `λ ≤ 1/3`, well inside the band --- so
this hypothesis is removable by replaying the descent decomposition in the
regime file.  Until that is done it is named rather than hidden, and this
reduction is strictly weaker than its `λ`-free counterpart. -/
theorem greendlingerConclusionSharp_of_three_factor [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    (hregime : ∀ w : List (α × Bool), TwoFactorRegime R w)
    (h : ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
      ∀ n : ℕ, 3 ≤ n → IsMinimalConjProduct R n (FreeGroup.mk w) →
        ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
          u <:+: w ∧ u <+: r ∧
            (1 - 3 * lam) * (r.length : ℚ) < (u.length : ℚ)) :
    GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨n, hmin⟩ :=
    exists_isMinimalConjProduct_of_mem_normalClosure R (FreeGroup.mk w) hmem
  rcases le_or_gt n 2 with hle | hgt
  · exact greendlingerSharp_of_isMinimalConjProduct_le_two hlam0 hlam hR hRne
      hmetric hw hwne hle hmin (hregime w)
  · exact h w hw hwne n (by omega) hmin

end SmallCancellationRouter
end GroupApproximation
