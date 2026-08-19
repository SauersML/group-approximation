import GroupApproximation.Sofic.GreendlingerInduction

/-!
# Two disjoint pieces, when the overhang is long

`GreendlingerInduction` states the strengthening the three-factor induction
needs -- `TwoPieceConclusion`, *two disjoint* subwords each more than half of a
symmetrized relator -- and proves it suffices.  It does not prove it, not even
in the two-factor case that `GreendlingerRegime` closes for the one-piece
conclusion.  This file closes one of the two branches of that base case, and
in doing so locates the remaining obligation precisely.

## Where the second piece is

The natural guess is that the two pieces are one per factor: the surviving part
of the first rotation inside `P'`, the surviving part of the second inside `B'`.
That guess is right in one branch and *wrong* in the other, which is why the
base case is not immediate from the mirror.

In the regime `|c'| ≤ |c|` of `regime_cases`, the first conjugator overhangs the
second by `q`, with `c = c' ++ q` and `q` a prefix of the second rotation
(`exists_overlap_of_cancellation`).  The destroyed block eats `q ++ invRev E`
out of `t'`, where `E` is the overlap.  `C'(1/6)` bounds `E` -- it is a piece,
so `6|E| < |t'|` -- and says nothing whatever about `q`.  So when `q` is long
the second rotation may be eaten past its own half, and no piece survives in
`B'` at all.

But then `q` is itself more than half of `t'`, because `q` is a *prefix* of
`t'`.  So both pieces live in `P'`, consecutively:

```text
    P'  =  c'  ++  q  ++  t.take (|t| − |E|)  ++  d
                   ^^^       ^^^^^^^^^^^^^^^
                   > ½ t'      > ½ t
```

That is `twoPiece_of_long_overhang`.  The second subword is more than half of
`t` for the reason the one-piece case already gives: the eaten suffix is a
piece, so `6|E| < |t|`, far more than the `2|E| < |t|` needed.

## What this leaves

The complementary branch -- `2(|q| + |E|) < |t'|`, where the surviving suffix
of `t'` really is a piece inside `B'` -- is the mirror of the argument above.
Between the two lies the band

```text
    |t'| − 2|E|  ≤  2|q|  ≤  |t'|,
```

of width `2|E| < |t'|/3`, in which `q` is a prefix of `t'` longer than `|t'|/3`
that is simultaneously a suffix of the first conjugator.  Neither minimality
reaches it: the factor count is spent on `hcoin`, and the weight is stable
there, since sliding `q` into the second conjugator (`mk_palindrome_slide`)
*lengthens* the total by `|q|`, and sliding it out of the first would need
`invRev q` to be a suffix of `t`, which nothing supplies.  That band is the
open obligation; `metadata/LITERATURE_QUARANTINE.md` records it as such.

Depends on `C'(1/6)` exactly where `GreendlingerPiece` does.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The surviving prefix, as a decomposition -/

/-- **`infix_take_of_bounded_cancellation`, with the witness kept.**  The
descent's quantitative case exports only that `t.take (|t| − k)` occurs in `P'`;
the two-piece conclusion needs to know *where*, because it has to put a second
subword in front of it.  Same bookkeeping, different conclusion. -/
theorem exists_split_take_of_bounded_cancellation
    {c t P' M : List (α × Bool)} {k : ℕ}
    (heq : palindrome c t = P' ++ M) (hk : k ≤ t.length)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + k) :
    ∃ d : List (α × Bool), P' = c ++ (t.take (t.length - k) ++ d) := by
  set t₁ := t.take (t.length - k) with ht₁
  set t₂ := t.drop (t.length - k) with ht₂
  have hsplit : t₁ ++ t₂ = t := List.take_append_drop _ t
  have hlen₂ : t₂.length = k := by
    rw [ht₂, List.length_drop]
    omega
  have hsuf : M <:+ (c ++ t₁) ++ (t₂ ++ FreeGroup.invRev c) := by
    refine ⟨P', ?_⟩
    rw [← heq]
    unfold palindrome
    rw [← hsplit]
    simp only [List.append_assoc]
  have hlenY : M.length ≤ (t₂ ++ FreeGroup.invRev c).length := by
    rw [List.length_append, hlen₂]
    omega
  obtain ⟨d, hd⟩ := suffix_of_suffix_append hsuf hlenY
  have hP' : P' = (c ++ t₁) ++ d := by
    have hcancel : P' ++ M = ((c ++ t₁) ++ d) ++ M := by
      rw [← heq]
      unfold palindrome
      rw [← hsplit]
      simp only [List.append_assoc]
      rw [← hd]
    exact List.append_cancel_right hcancel
  refine ⟨d, ?_⟩
  rw [hP', List.append_assoc]

/-! ## The long-overhang branch -/

/-- **Two disjoint pieces, both in `P'`.**  When the first conjugator overhangs
the second by `q` and `q` is already more than half of the second rotation, the
two subwords the strengthened conclusion asks for are `q` and the surviving
prefix of the first rotation, consecutive inside `P'`.

Nothing of `B'` is used, which is the content: in this branch the second factor
contributes its piece through the *conjugator* of the first palindrome, not
through what survives of its own rotation. -/
theorem twoPiece_of_long_overhang {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c c' q t t' P' M B' E : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hc : c = c' ++ q) (hq : q <+: t')
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E))
    (hlong : t'.length < 2 * q.length) :
    TwoPieceConclusion R (P' ++ B') := by
  have h6 := six_mul_length_lt_of_eaten hmetric ht hE hpiece
  have hEle : E.length ≤ t.length := hE.length_le
  obtain ⟨d, hP'⟩ := exists_split_take_of_bounded_cancellation heq hEle hlen
  refine ⟨c', q, [], t.take (t.length - E.length), d ++ B', ?_,
    ⟨t', ht', hq, hlong⟩, ⟨t, ht, List.take_prefix _ _, ?_⟩⟩
  · rw [hP', hc]
    simp only [List.append_assoc, List.nil_append]
  · have hlenu : (t.take (t.length - E.length)).length = t.length - E.length := by
      rw [List.length_take]
      omega
    omega

/-- The one-piece conclusion of the long-overhang branch, for callers that only
want it: two disjoint pieces are strictly more than the gate asks for. -/
theorem greendlinger_of_long_overhang {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c c' q t t' P' M B' E : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hc : c = c' ++ q) (hq : q <+: t')
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E))
    (hlong : t'.length < 2 * q.length) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧ s.length < 2 * u.length :=
  greendlinger_of_twoPieceConclusion
    (twoPiece_of_long_overhang hmetric ht ht' heq hc hq hE hlen hpiece hlong)

end SmallCancellationRouter
end GroupApproximation
