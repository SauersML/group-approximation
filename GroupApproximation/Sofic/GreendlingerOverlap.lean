import GroupApproximation.Sofic.GreendlingerPiece

/-!
# Where the eaten overlap sits, and why it is a piece

`GreendlingerPiece` closed the descent's second case from the hypothesis that
the overlap a cancellation eats out of a rotation **is a piece**.  That
hypothesis was the whole of what the descent still owed.  This file pays it.

## What a piece actually needs

`IsPiece` asks for **two distinct** symmetrized relators sharing the overlap as
a prefix.  One of the two is free: the overlap `E` is a suffix of the rotation
`t` it is eaten out of, so `invRev E` prefixes `invRev t`, and `symmetrization`
is closed under `invRev`.  The second comes from the other side of the product
--- an overlap is eaten *against* something, and that something is the next
factor's rotation.  So the missing step splits in two:

* **locate** `invRev E` inside the next palindrome, and
* **distinguish** the relator it lands in from `invRev t`.

## Locating it

Three moves, in the order the descent makes them.

* `eaten_split` --- a cancellation that reaches past the trailing conjugator
  eats *all* of it: the destroyed block is `E ++ invRev c`, with `E` a suffix of
  `c ++ t`, and a suffix of `t` itself once the block is no longer than
  `|invRev c| + |t|` (`eaten_suffix_of_le`).
* `invRev_eaten_block` --- the matching prefix of the next word is therefore
  `c ++ invRev E`: the formal inverse is an anti-homomorphism, so the *leading*
  conjugator reappears in front of the overlap.  This is why the two
  conjugators have to be compared at all.
* `exists_split_of_overlap_prefix` --- if the next conjugator is no longer than
  `c`, it is a prefix of `c`, say `c = c' ++ q`, and `q ++ invRev E` is a prefix
  of the next rotation.  A prefix starting `|q|` letters in is a prefix of the
  rotation by `|q|` (`prefix_rotate_of_append_prefix`), and `symmetrization` is
  rotation-closed --- which is precisely why the classical definition of a piece
  may speak only of *prefixes*.

## Distinguishing them

This is where minimality of the expression is spent, and the mechanism is
`mk_palindrome_mul_eq_one_of_coincidence`: **if the overlap lands in the very
relator it was eaten out of, the two factors are mutually inverse.**

The computation is forced.  The overhang `q` of the first conjugator past the
second is the prefix of the next rotation that the overlap starts after, so
`q = t'.take |q|`; and a rotation is a conjugate by exactly that prefix
(`mk_rotate_conj`).  So `invRev t = t'.rotate |q|` reads

`(mk t)⁻¹ = (mk q)⁻¹ * mk t' * mk q`,

and with `mk c = mk c' * mk q` the first palindrome spells
`mk c' * (mk t')⁻¹ * (mk c')⁻¹`, the inverse of what the second spells.  Their
product is `1`.

A shortest expression has no such pair --- deleting both factors would shorten
it by two --- so in the descent the two relators are distinct, the overlap is a
piece, and `C'(1/6)` applies.  `greendlinger_of_two_palindromes` is the two-
factor descent with no distinctness hypothesis left: it asks only that the two
factors not cancel, which is what minimality says.

Unconditional; the `C'(1/6)` hypothesis enters only through
`greendlinger_of_piece_cancellation`, in the last two statements.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Splitting the eaten block at the trailing conjugator -/

/-- A suffix long enough to reach past the last block of a concatenation
contains that block whole, and what precedes it is a suffix of the first
block. -/
theorem suffix_split_of_length_le {X Y M : List α} (h : M <:+ X ++ Y)
    (hlen : Y.length ≤ M.length) : ∃ E, M = E ++ Y ∧ E <:+ X := by
  have hY : Y <:+ X ++ Y := ⟨X, rfl⟩
  obtain ⟨E, hE⟩ := List.suffix_of_suffix_length_le hY h hlen
  obtain ⟨s, hs⟩ := h
  refine ⟨E, hE.symm, s, ?_⟩
  have hcancel : s ++ E ++ Y = X ++ Y := by
    rw [List.append_assoc, hE]
    exact hs
  exact List.append_cancel_right hcancel

/-- **The eaten block, split.**  A cancellation reaching past the trailing
conjugator destroys all of it, and the rest of the block is a suffix of
`c ++ t`. -/
theorem eaten_split {c t M : List (α × Bool)} (h : M <:+ palindrome c t)
    (hlen : (FreeGroup.invRev c).length ≤ M.length) :
    ∃ E, M = E ++ FreeGroup.invRev c ∧ E <:+ c ++ t := by
  refine suffix_split_of_length_le ?_ hlen
  unfold palindrome at h
  exact h

/-- If the block does not reach past the rotation, what it eats beyond the
conjugator is a suffix of the rotation itself. -/
theorem eaten_suffix_of_le {c t M E : List (α × Bool)}
    (hM : M = E ++ FreeGroup.invRev c) (hE : E <:+ c ++ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + t.length) : E <:+ t := by
  refine suffix_of_suffix_append hE ?_
  have h : M.length = E.length + (FreeGroup.invRev c).length := by
    rw [hM, List.length_append]
  omega

/-- **The matching prefix carries the leading conjugator.**  Because `invRev` is
an anti-homomorphism, the block the product destroys in the *second* word is the
overlap with the *first* word's leading conjugator in front of it. -/
theorem invRev_eaten_block {c E M : List (α × Bool)}
    (hM : M = E ++ FreeGroup.invRev c) :
    FreeGroup.invRev M = c ++ FreeGroup.invRev E := by
  rw [hM, FreeGroup.invRev_append, FreeGroup.invRev_invRev]

/-! ## Locating the overlap in the next factor -/

/-- A prefix that begins `|q|` letters into a word is a prefix of the rotation
of that word by `|q|`.  This is why pieces may be defined by prefixes alone:
`symmetrization` is rotation-closed, so an occurrence anywhere is an occurrence
at the front of some member. -/
theorem prefix_rotate_of_append_prefix {q p l : List (α × Bool)}
    (h : q ++ p <+: l) : p <+: l.rotate q.length := by
  obtain ⟨z, hz⟩ := h
  have hl : l = q ++ (p ++ z) := by
    rw [← hz, List.append_assoc]
  have hlen : q.length ≤ l.length := by
    rw [hl, List.length_append]
    omega
  refine ⟨z ++ q, ?_⟩
  rw [List.rotate_eq_drop_append_take hlen, hl, List.drop_left, List.take_left,
    List.append_assoc]

/-- **Where the overlap starts.**  If the inverse of the destroyed block --- the
leading conjugator followed by the overlap --- prefixes the next palindrome, and
the next conjugator is no longer than the first, then the first conjugator
overhangs the second by some `q`, and the overlap begins exactly `q` letters
into the next rotation.

The overhang `q` is what the whole distinctness argument turns on: it is
simultaneously a suffix of `c` and a prefix of `t'`. -/
theorem exists_split_of_overlap_prefix {c c' t' p : List (α × Bool)}
    (hpre : c ++ p <+: palindrome c' t')
    (hle : c'.length ≤ c.length)
    (hfit : c.length - c'.length + p.length ≤ t'.length) :
    ∃ q : List (α × Bool), c = c' ++ q ∧ q ++ p <+: t' := by
  have hP : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
    unfold palindrome
    rw [List.append_assoc]
  have hc'pre : c' <+: palindrome c' t' := by
    rw [hP]
    exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
  have hcpre : c <+: palindrome c' t' :=
    (show c <+: c ++ p from ⟨p, rfl⟩).trans hpre
  obtain ⟨q, hq⟩ := List.prefix_of_prefix_length_le hc'pre hcpre hle
  have hqlen : q.length = c.length - c'.length := by
    have hlen := congrArg List.length hq
    rw [List.length_append] at hlen
    omega
  refine ⟨q, hq.symm, ?_⟩
  have h1 : c' ++ (q ++ p) <+: c' ++ (t' ++ FreeGroup.invRev c') := by
    rw [← List.append_assoc, hq, ← hP]
    exact hpre
  have hqp : q ++ p <+: t' ++ FreeGroup.invRev c' :=
    (List.prefix_append_right_inj c').mp h1
  refine List.prefix_of_prefix_length_le hqp ⟨FreeGroup.invRev c', rfl⟩ ?_
  rw [List.length_append]
  omega

/-! ## The overlap is a piece unless the two relators coincide -/

/-- **The dichotomy.**  An overlap eaten out of one symmetrized relator and
landing in another is a piece as soon as the two are distinct words.

Both halves of `IsPiece` are in hand: `invRev E` prefixes `invRev t` because
`invRev` turns suffixes into prefixes, and it prefixes `t'.rotate k` by
hypothesis.  Only distinctness is missing, and distinctness is not a statement
about pieces at all --- it is a statement about the expression. -/
theorem isPiece_of_overlap {R : Set (List (α × Bool))}
    {t t' E : List (α × Bool)} {k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hE : E <:+ t)
    (hpre : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k) :
    IsPiece (symmetrization R) (FreeGroup.invRev E) :=
  isPiece_of_prefix_two (invRev_mem_symmetrization ht)
    (rotate_mem_symmetrization ht' k) hne (invRev_prefix_of_suffix hE) hpre

/-- **The descent's second case, with the piece hypothesis discharged.**  What
stands in its place is the distinctness of two words. -/
theorem greendlinger_of_distinct_overlap {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t t' P' M B' E : List (α × Bool)} {k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpre : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧ s.length < 2 * u.length :=
  greendlinger_of_piece_cancellation hRne hmetric ht heq hE hlen
    (isPiece_of_overlap ht ht' hE hpre hne)

/-! ## The coincidence collapses the expression -/

/-- **A rotation is a conjugate by the prefix rotated past.**  Splitting `s` at
`j`, the rotation is `d ++ z` where `s` is `z ++ d`, and `d * z = z⁻¹ * (z * d)
* z`. -/
theorem mk_rotate_conj (s : List (α × Bool)) (j : ℕ) (hj : j ≤ s.length) :
    FreeGroup.mk (s.rotate j)
      = (FreeGroup.mk (s.take j))⁻¹ * FreeGroup.mk s * FreeGroup.mk (s.take j) := by
  have hsplit : FreeGroup.mk s
      = FreeGroup.mk (s.take j) * FreeGroup.mk (s.drop j) := by
    rw [FreeGroup.mul_mk, List.take_append_drop]
  have hrot : FreeGroup.mk (s.rotate j)
      = FreeGroup.mk (s.drop j) * FreeGroup.mk (s.take j) := by
    rw [FreeGroup.mul_mk, ← List.rotate_eq_drop_append_take hj]
  rw [hrot, hsplit]
  group

/-- **The coincidence, computed.**  If the overlap lands in the very relator it
was eaten out of --- that is, if `invRev t` *is* the rotation of `t'` the
overlap prefixes --- then the two palindromes spell mutually inverse elements.

This is the exact sense in which the descent's distinctness is a statement about
the expression: a shortest expression contains no two factors whose product is
trivial, because deleting both would shorten it by two.  Everything else in the
identification of the overlap as a piece is bookkeeping; this is the step where
minimality is spent. -/
theorem mk_palindrome_mul_eq_one_of_coincidence {c c' q t t' : List (α × Bool)}
    (hc : c = c' ++ q) (hq : q <+: t')
    (hrot : FreeGroup.invRev t = t'.rotate q.length) :
    FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') = 1 := by
  have hqle : q.length ≤ t'.length := hq.length_le
  have hqtake : t'.take q.length = q := by
    obtain ⟨z, hz⟩ := hq
    rw [← hz, List.take_left]
  have hinv : (FreeGroup.mk t)⁻¹
      = (FreeGroup.mk q)⁻¹ * FreeGroup.mk t' * FreeGroup.mk q := by
    rw [FreeGroup.inv_mk, hrot, mk_rotate_conj t' q.length hqle, hqtake]
  have ht : FreeGroup.mk t
      = ((FreeGroup.mk q)⁻¹ * FreeGroup.mk t' * FreeGroup.mk q)⁻¹ := by
    rw [← hinv, inv_inv]
  have hmc : FreeGroup.mk c = FreeGroup.mk c' * FreeGroup.mk q := by
    rw [hc, FreeGroup.mul_mk]
  rw [mk_palindrome, mk_palindrome, hmc, ht]
  group

/-- **The coincidence, in the other conjugator regime.**  If the *second*
conjugator overhangs the first by `y`, and the second rotation is the rotation
of the first inverted one by `y`, the two palindromes again spell mutually
inverse elements. -/
theorem mk_palindrome_mul_eq_one_of_coincidence' {c c' y t t' : List (α × Bool)}
    (hc' : c' = c ++ y) (hy : y <+: FreeGroup.invRev t)
    (hrot : t' = (FreeGroup.invRev t).rotate y.length) :
    FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') = 1 := by
  have hyle : y.length ≤ (FreeGroup.invRev t).length := hy.length_le
  have hytake : (FreeGroup.invRev t).take y.length = y := by
    obtain ⟨z, hz⟩ := hy
    rw [← hz, List.take_left]
  have hmt' : FreeGroup.mk t'
      = (FreeGroup.mk y)⁻¹ * (FreeGroup.mk t)⁻¹ * FreeGroup.mk y := by
    rw [hrot, mk_rotate_conj (FreeGroup.invRev t) y.length hyle, hytake,
      ← FreeGroup.inv_mk]
  have hmc' : FreeGroup.mk c' = FreeGroup.mk c * FreeGroup.mk y := by
    rw [hc', FreeGroup.mul_mk]
  rw [mk_palindrome, mk_palindrome, hmc', hmt']
  group

/-! ## The overlap, extracted from the cancellation -/

/-- **The geometry of the second case, in one step.**  A destroyed block that
reaches past the trailing conjugator but not past the rotation, and whose
matching prefix fits inside the next rotation, exhibits the overlap `E` together
with the overhang `q` that positions it.

The three length hypotheses are the three ways the cancellation could fail to be
this shape: it could stop inside the trailing conjugator (that is
`GreendlingerDescent`'s free case), it could eat the whole rotation and reach
into the leading conjugator, or the matching prefix could run past the next
rotation into its trailing conjugator. -/
theorem exists_overlap_of_cancellation {c t c' t' P' M : List (α × Bool)}
    (heq : palindrome c t = P' ++ M)
    (hpre : FreeGroup.invRev M <+: palindrome c' t')
    (hlow : (FreeGroup.invRev c).length ≤ M.length)
    (hhigh : M.length ≤ (FreeGroup.invRev c).length + t.length)
    (hle : c'.length ≤ c.length)
    (hfit : c.length - c'.length + M.length ≤ c.length + t'.length) :
    ∃ E q : List (α × Bool), E <:+ t ∧ c = c' ++ q ∧ q <+: t' ∧
      M.length ≤ (FreeGroup.invRev c).length + E.length ∧
      FreeGroup.invRev E <+: t'.rotate q.length := by
  have hMsuf : M <:+ palindrome c t := ⟨P', heq.symm⟩
  obtain ⟨E, hM, hEsuf⟩ := eaten_split hMsuf hlow
  have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
  have hEl : (FreeGroup.invRev E).length = E.length := FreeGroup.invRev_length
  have hMlen : M.length = E.length + (FreeGroup.invRev c).length := by
    rw [hM, List.length_append]
  have hinv : FreeGroup.invRev M = c ++ FreeGroup.invRev E := invRev_eaten_block hM
  rw [hinv] at hpre
  obtain ⟨q, hcq, hqp⟩ := exists_split_of_overlap_prefix hpre hle (by omega)
  refine ⟨E, q, eaten_suffix_of_le hM hEsuf hhigh, hcq, ?_, by omega, ?_⟩
  · exact (show q <+: q ++ FreeGroup.invRev E from ⟨FreeGroup.invRev E, rfl⟩).trans hqp
  · exact prefix_rotate_of_append_prefix hqp

/-- **The two-factor descent, with nothing owed but the length regime.**  For a
product of two palindromes whose factors do not cancel, the Greendlinger
conclusion holds: either the cancellation stays inside the trailing conjugator
and the whole first rotation survives, or it eats an overlap, and that overlap
is a piece --- because were it not, the two factors would be mutually inverse.

The hypothesis `hcoin` is exactly what minimality of the expression supplies. -/
theorem greendlinger_of_two_palindromes {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' P' M B' : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hpre : FreeGroup.invRev M <+: palindrome c' t')
    (hhigh : M.length ≤ (FreeGroup.invRev c).length + t.length)
    (hle : c'.length ≤ c.length)
    (hfit : c.length - c'.length + M.length ≤ c.length + t'.length)
    (hcoin : FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') ≠ 1) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧ s.length < 2 * u.length := by
  rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
  · exact greendlinger_of_short_cancellation hRne ht heq hshort
  · obtain ⟨E, q, hEt, hcq, hqt, hElen, hEpre⟩ :=
      exists_overlap_of_cancellation heq hpre hlong.le hhigh hle hfit
    refine greendlinger_of_distinct_overlap hRne hmetric ht ht' heq hEt hElen
      hEpre ?_
    intro hcon
    exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt hcon)

end SmallCancellationRouter
end GroupApproximation
