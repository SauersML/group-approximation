import GroupApproximation.Sofic.GreendlingerCancellation

/-!
# The first case of the descent: a relator the cancellation never reaches

`GreendlingerCancellation` shows that multiplying two reduced words destroys a
single matched block `M`.  In the descent, the two words are palindromes
`palindrome c t = c ++ t ++ invRev c` around rotations of relators, and the
question is how much of a rotation the product destroys.

This file settles the case in which it destroys none of it: **if the destroyed
block is no longer than the trailing conjugator, the whole rotation survives as
a contiguous subword of the product.**  That is already the Greendlinger
conclusion, in its strongest form, for that factor.

The argument is length bookkeeping and nothing else.  A suffix short enough to
fit inside the last block of a concatenation is a suffix of that block
(`suffix_of_suffix_append`); so `M` is a suffix of `invRev c`, the surviving
prefix is `c ++ t ++ d` for the complementary `d`, and `t` sits inside it.  No
small-cancellation hypothesis is used, which is the point: this case is free,
and the `C'(1/6)` bound is needed only for the *other* case, where the
cancellation eats into the rotation and the overlap it eats is a piece.

`greendlinger_of_infix` records the bridge those cases share: a symmetrized
relator occurring as a contiguous subword gives the Greendlinger conclusion
outright, since `|t| < 2|t|` is just nonemptiness.

Unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Length bookkeeping -/

/-- A suffix short enough to fit inside the last block of a concatenation is a
suffix of that block. -/
theorem suffix_of_suffix_append {M X Y : List α} (h : M <:+ X ++ Y)
    (hlen : M.length ≤ Y.length) : M <:+ Y := by
  obtain ⟨s, hs⟩ := h
  have hXpre : X <+: s ++ M := by
    rw [hs]
    exact ⟨Y, rfl⟩
  have hspre : s <+: s ++ M := ⟨M, rfl⟩
  have hlenX : X.length ≤ s.length := by
    have hcount := congrArg List.length hs
    simp only [List.length_append] at hcount
    omega
  obtain ⟨s', hs'⟩ := List.prefix_of_prefix_length_le hXpre hspre hlenX
  refine ⟨s', ?_⟩
  refine List.append_cancel_left (l := X) ?_
  rw [← List.append_assoc, hs', hs]

/-! ## The relator the cancellation never reaches -/

/-- **A cancellation confined to the trailing conjugator leaves the rotation
whole.** -/
theorem infix_of_short_cancellation {c t P' M : List (α × Bool)}
    (heq : palindrome c t = P' ++ M)
    (hlen : M.length ≤ (FreeGroup.invRev c).length) : t <:+: P' := by
  have hsuf : M <:+ (c ++ t) ++ FreeGroup.invRev c := ⟨P', heq.symm⟩
  obtain ⟨d, hd⟩ := suffix_of_suffix_append hsuf hlen
  have hP' : P' = (c ++ t) ++ d := by
    refine List.append_cancel_right (l := M) ?_
    rw [← heq]
    unfold palindrome
    rw [← hd, List.append_assoc]
  rw [hP']
  exact ⟨c, d, rfl⟩

/-- **The first case of the descent.**  In a product whose reduced form is
`P' ++ B'`, a factor whose destroyed block stays inside its trailing conjugator
contributes its whole rotation as a subword. -/
theorem infix_of_two_factor_short {c t P' M B' : List (α × Bool)}
    (heq : palindrome c t = P' ++ M)
    (hlen : M.length ≤ (FreeGroup.invRev c).length) :
    t <:+: P' ++ B' :=
  (infix_of_short_cancellation heq hlen).trans ⟨[], B', by simp⟩

/-! ## The bridge every case ends at -/

/-- **A symmetrized relator occurring as a subword gives the conclusion.**  The
inequality the gate asks for, `|s| < 2|u|`, is just nonemptiness when `u` is the
whole relator. -/
theorem greendlinger_of_infix {R : Set (List (α × Bool))} {t w : List (α × Bool)}
    (ht : t ∈ symmetrization R) (htne : t ≠ []) (hinf : t <:+: w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  refine ⟨t, ht, t, hinf, List.prefix_refl _, ?_⟩
  have hpos : 0 < t.length := List.length_pos_iff.mpr htne
  omega

/-- The two combined: a factor the cancellation never reaches settles the
Greendlinger conclusion for the whole product. -/
theorem greendlinger_of_short_cancellation {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) {c t P' M B' : List (α × Bool)}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlen : M.length ≤ (FreeGroup.invRev c).length) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧ s.length < 2 * u.length :=
  greendlinger_of_infix ht (ne_nil_of_mem_symmetrization hRne ht)
    (infix_of_two_factor_short heq hlen)

end SmallCancellationRouter
end GroupApproximation
