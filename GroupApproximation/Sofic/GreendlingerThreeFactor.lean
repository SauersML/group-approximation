import GroupApproximation.Sofic.GreendlingerTwoPieceRegime

/-!
# Expressions with three or more conjugate factors

`GreendlingerRegime` closes the gate for every element whose expressions can be
taken with at most two conjugate factors.  This file carries the descent to
expressions of **arbitrary** length, and so to the three-or-more case that
`GreendlingerInduction.greendlingerConclusion_of_three_factor` isolated as all
that is left.

## The conclusion has to be located, and it has to carry slack

`GreendlingerInduction` observed that the bare conclusion --- *some* subword of
`w` is more than half a relator --- does not survive multiplication by another
factor, and proposed the two-disjoint-pieces strengthening.  That strengthening
is false (`GreendlingerTwoPieceRegime` carries the witness).  What survives is
the conclusion together with the **position** of the subword, and with a
**slack** in that position:

`GreendlingerAt R n w` --- `w = A ++ u ++ C` with `n ≤ |A|` and `u` more than
half of a symmetrized relator.

The statement the induction proves is not `GreendlingerAt R |c₁| w` but

  `∀ j, 6j < |t₁| → GreendlingerAt R (|c₁| + j) w`,

a whole family, one for each offset `j` below a sixth of the leading rotation.
The slack is free: a base producer keeps five sixths of its rotation and needs
only a half, so it can begin its subword `j` letters late for any such `j`.  And
the slack is exactly what the descent needs, because the amount a factor eats
off the *front* of what the rest of the product spells is a piece of the next
rotation, hence smaller than a sixth of it --- smaller than the slack the next
stage was carrying.  So the subword is never chewed: **the case that eats into
the tail's subword cannot occur.**

## The descent, factor by factor

For a minimal expression whose two leading factors are in palindromic normal
form, the leading cancellation `M` falls into four cases:

* `|M| ≤ |c|` --- the block stays inside the trailing conjugator, the whole
  rotation `t` survives.  **No hypothesis at all**, at any length.
* `|c| < |M|`, `|c'| ≤ |c|` --- the overlap the block eats out of `t` is a
  piece, because otherwise the two factors would cancel, which minimality of the
  factor count forbids.  `C'(1/6)` leaves five sixths of `t` standing.
* `|c| < |c'|`, `|M| ≤ |c'|` --- the block's image is buried in the second
  conjugator.  `eaten_le_of_minimal_reroute` bounds what it eats by half the
  rotation, and the tail's own subword, carried at offset `0`, is untouched.
* `|c| < |c'| < |M|` --- the block reaches past the second conjugator and meets
  the second rotation in `v`.  Then `v` is a piece, so `6|v| < |t'|`, so the
  tail's subword carried at offset `|v|` begins at or after `|M|` and is again
  untouched; and `overhang_le_of_minimal_reroute_meet` bounds the overhang by
  what the rotation has left, which keeps the position bookkeeping.

The last two cases are inheritance, and the two weight moves proved here are
what makes their arithmetic work.  Nothing is special to two or three factors:
the same four cases run at every length.

## What is left

One statement, `LeadingConfinement`: the block a factor loses to the rest of the
product is matched inside the *next factor's* palindrome.  It is what lets the
block be read against a rotation at all, and every case above except the free
one uses it.  It is not a small cancellation hypothesis and it mentions no
pieces; it is one prefix statement about the words the decomposition produces.

Half of it is now a theorem.  `eaten_lt_of_long_next_conjugator` settles the
regime where the *next* conjugator is the longer one: there, everything the
block eats past `c'` is matched against letters of the leading rotation, so it
is a piece of the next rotation, `C'(1/6)` bounds it by a sixth, and the next
factor keeps more than five twelfths --- so the block stops well inside, and
stops early enough for the tail's subword to survive.  That theorem needs only
the survival bound, which every case of the descent delivers.

What is left is the other regime: the leading conjugator the longer, running
along the next rotation itself.  There the eaten part is a hug plus a piece, the
two weight moves give five twelfths kept against seven twelfths eaten, and those
cross --- with `|t'| = 60` the moves permit `|q| = 17, |p| = 9, |y₂| = 25,
|v₂| = 9`, every inequality holding while the block eats the whole survivor.  A
block that wins that race runs into the factors after the next one, which is
what two non-adjacent factors sharing an arc looks like.

Two things are known about such a block, and a continuation should start from
them.  First, past the next factor it lands among *relator* letters of the
factor after that --- that chunk begins with its own conjugator and the block
enters past it --- so the segment is again a piece, and a block that overruns
eats two pieces, under a third of its own rotation, which is better than the
half the conclusion needs.  Second, an overrun forces the next factor's survivor
**below** two thirds (a hug is at most a half, a piece under a sixth), while a
factor whose own block overruns keeps **more** than two thirds: so overruns
cannot occur at two consecutive levels.  What is not closed is a block that
overruns and then exhausts the chunk it lands in, reaching the conjugator of a
factor it is not adjacent to, where no reroute identity applies --- a reroute
moves one factor past its neighbour and no further.
`Sofic/GreendlingerChunks` makes that cascade a definable object.

Depends on `C'(1/6)` exactly where `GreendlingerRegime` does.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The conclusion, with its subword located -/

/-- **The Greendlinger conclusion, located.**  The word splits as `A ++ u ++ C`
with `u` more than half of a symmetrized relator and `A` at least `n` letters
long: the subword begins no earlier than position `n`.

Position is what the descent inherits.  A subword beginning past the block a
leading factor destroys survives that factor, and nothing weaker than a
statement about position can say so. -/
def GreendlingerAt (R : Set (List (α × Bool))) (n : ℕ) (w : List (α × Bool)) :
    Prop :=
  ∃ A u C : List (α × Bool), w = A ++ u ++ C ∧ n ≤ A.length ∧
    ∃ s ∈ symmetrization R, u <+: s ∧ s.length < 2 * u.length

/-- Forgetting where the subword is gives back the gate's own conclusion. -/
theorem greendlinger_of_greendlingerAt {R : Set (List (α × Bool))} {n : ℕ}
    {w : List (α × Bool)} (h : GreendlingerAt R n w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  obtain ⟨A, u, C, hw, -, s, hs, hpre, hlt⟩ := h
  refine ⟨s, hs, u, ⟨A, C, ?_⟩, hpre, hlt⟩
  rw [hw]

/-- A subword located past `n` is located past anything shorter. -/
theorem GreendlingerAt.mono {R : Set (List (α × Bool))} {m n : ℕ}
    {w : List (α × Bool)} (h : GreendlingerAt R n w) (hmn : m ≤ n) :
    GreendlingerAt R m w := by
  obtain ⟨A, u, C, hw, hlen, hs⟩ := h
  exact ⟨A, u, C, hw, le_trans hmn hlen, hs⟩

/-! ## The located producers, with slack -/

/-- Splitting a prefix in two: `take (a + b)` is `take a` followed by the next
`b` letters.  Mathlib states this only for `take` against `append`; the descent
needs it against `drop`, so it is proved here. -/
theorem take_add_split {β : Type*} :
    ∀ (a : ℕ) (l : List β) (b : ℕ),
      l.take (a + b) = l.take a ++ (l.drop a).take b := by
  intro a
  induction a with
  | zero =>
      intro l b
      simp
  | succ a ih =>
      intro l b
      cases l with
      | nil => simp
      | cons x xs =>
          have hab : a + 1 + b = a + b + 1 := by omega
          rw [hab]
          simpa using ih xs b

/-- **The quantitative case, located and with slack.**  A cancellation reaching
`k` letters past the trailing conjugator leaves `t.take (|t| - k)` standing; the
subword may be started `j` letters later still, at position exactly `|c| + j`,
as long as `2(k + j) < |t|`.

The slack `j` is what the descent spends: it is carried into the next stage and
absorbs the piece that stage's factor eats. -/
theorem greendlingerAt_of_bounded_cancellation {R : Set (List (α × Bool))}
    {c t P' M B' : List (α × Bool)} {k j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + k)
    (hk : 2 * (k + j) < t.length) :
    GreendlingerAt R (c.length + j) (P' ++ B') := by
  have hkle : k ≤ t.length := by omega
  obtain ⟨d, hP'⟩ := exists_split_take_of_bounded_cancellation heq hkle hlen
  have hjle : j ≤ t.length := by omega
  have hsplit : t.take (t.length - k)
      = t.take j ++ (t.drop j).take (t.length - k - j) := by
    have hb := take_add_split j t (t.length - k - j)
    rw [show j + (t.length - k - j) = t.length - k from by omega] at hb
    exact hb
  refine ⟨c ++ t.take j, (t.drop j).take (t.length - k - j), d ++ B', ?_, ?_,
    t.rotate j, rotate_mem_symmetrization ht j, ?_, ?_⟩
  · rw [hP', hsplit]
    simp only [List.append_assoc]
  · rw [List.length_append, List.length_take]
    omega
  · rw [List.rotate_eq_drop_append_take hjle]
    exact (List.take_prefix _ _).trans ⟨t.take j, rfl⟩
  · rw [List.length_rotate, List.length_take, List.length_drop]
    omega

/-- **The free case, located and with slack.**  A cancellation confined to the
trailing conjugator leaves the whole rotation standing, so any offset below a
sixth of it is available. -/
theorem greendlingerAt_of_short_cancellation {R : Set (List (α × Bool))}
    {c t P' M B' : List (α × Bool)} {j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlen : M.length ≤ (FreeGroup.invRev c).length)
    (hj : 6 * j < t.length) :
    GreendlingerAt R (c.length + j) (P' ++ B') :=
  greendlingerAt_of_bounded_cancellation (k := 0) ht heq (by omega) (by omega)

/-- **The overlap case, located and with slack.**  When the leading conjugator
is the longer of the two, the overlap the block eats out of the leading rotation
is a piece --- were it not, the two factors would spell mutually inverse
elements --- so `C'(1/6)` leaves five sixths of that rotation standing, of which
a half suffices and a sixth may be spent on slack.

Unlike `greendlinger_of_two_palindromes_mirror`, which finds its subword inside
the *second* factor's survivor, this one finds it inside the first factor's, and
that is what makes it usable at the head of an expression of any length: what
follows the leading factor is arbitrary. -/
theorem greendlingerAt_of_overlap {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' P' M B' : List (α × Bool)} {j : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hpre : FreeGroup.invRev M <+: palindrome c' t')
    (hhigh : M.length ≤ (FreeGroup.invRev c).length + t.length)
    (hle : c'.length ≤ c.length)
    (hfit : c.length - c'.length + M.length ≤ c.length + t'.length)
    (hcoin : FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') ≠ 1)
    (hj : 6 * j < t.length) :
    GreendlingerAt R (c.length + j) (P' ++ B') := by
  rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
  · exact greendlingerAt_of_short_cancellation ht heq hshort hj
  · obtain ⟨E, q, hEt, hcq, hqt, hElen, hEpre⟩ :=
      exists_overlap_of_cancellation heq hpre hlong.le hhigh hle hfit
    have hne : FreeGroup.invRev t ≠ t'.rotate q.length := by
      intro hcon
      exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt hcon)
    have hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E) :=
      isPiece_of_overlap ht ht' hEt hEpre hne
    have h6 := six_mul_length_lt_of_eaten hmetric ht hEt hpiece
    exact greendlingerAt_of_bounded_cancellation ht heq hElen (by omega)

/-! ## Inheriting a located subword through a factor -/

/-- **The induction step.**  A subword of what the rest of the product spells,
beginning at or after the block `M` the leading factor destroys, survives that
factor --- and lands at position `|c| + j`, because the block leaves at least
that many letters of the palindrome standing.

This is the whole of what the descent needs from the tail: not that the tail's
subword is anywhere in particular, only that it begins late enough. -/
theorem greendlingerAt_inherit {R : Set (List (α × Bool))}
    {c t P' M B' W : List (α × Bool)} {n j : ℕ}
    (heq : palindrome c t = P' ++ M)
    (hW : W = FreeGroup.invRev M ++ B')
    (hhigh : M.length + j ≤ c.length + t.length)
    (hn : M.length ≤ n)
    (h : GreendlingerAt R n W) :
    GreendlingerAt R (c.length + j) (P' ++ B') := by
  obtain ⟨A, u, C, hWeq, hAlen, s, hs, hupre, hlt⟩ := h
  have hMl : (FreeGroup.invRev M).length = M.length := FreeGroup.invRev_length
  have hMpre : FreeGroup.invRev M <+: W := ⟨B', hW.symm⟩
  have hApre : A <+: W := ⟨u ++ C, by rw [hWeq, List.append_assoc]⟩
  obtain ⟨D, hD⟩ := List.prefix_of_prefix_length_le hMpre hApre (by omega)
  have hlenA : (FreeGroup.invRev M).length + D.length = A.length := by
    have hb := congrArg List.length hD
    rw [List.length_append] at hb
    exact hb
  have hsplit : FreeGroup.invRev M ++ B'
      = FreeGroup.invRev M ++ (D ++ (u ++ C)) := by
    rw [← hW, hWeq, ← hD]
    simp only [List.append_assoc]
  have hB' : B' = D ++ (u ++ C) := List.append_cancel_left hsplit
  have hpal : (palindrome c t).length = c.length + t.length + c.length := by
    simp [palindrome, FreeGroup.invRev_length, Nat.add_assoc]
  have hlenP : P'.length + M.length = c.length + t.length + c.length := by
    have hb := congrArg List.length heq
    rw [List.length_append, hpal] at hb
    omega
  refine ⟨P' ++ D, u, C, ?_, ?_, s, hs, hupre, hlt⟩
  · rw [hB']
    simp only [List.append_assoc]
  · rw [List.length_append]
    omega

/-! ## Minimality is hereditary along every suffix -/

/-- A minimal expression is minimal for what it spells. -/
theorem IsMinimalConjExpr.self_eval [DecidableEq α] {R : Set (List (α × Bool))}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (h : IsMinimalConjExpr R e g) : IsMinimalConjExpr R e (conjEval e) := by
  rw [h.2.1]
  exact h

/-- **Every suffix of a minimal expression is minimal**, by iterating
`IsMinimalConjExpr.tail`.  The descent walks down an expression one factor at a
time, and this is what lets it treat each stage as a fresh minimal expression. -/
theorem isMinimalConjExpr_drop [DecidableEq α] {R : Set (List (α × Bool))} :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
      IsMinimalConjExpr R e g →
        IsMinimalConjExpr R (e.drop k) (conjEval (e.drop k)) := by
  intro k
  induction k with
  | zero =>
      intro e g h
      rw [List.drop_zero]
      exact h.self_eval
  | succ k ih =>
      intro e g h
      cases e with
      | nil =>
          rw [List.drop_nil]
          exact h.self_eval
      | cons x e' =>
          rw [List.drop_succ_cons]
          exact ih e' (conjEval e') h.tail

/-! ## The palindromic normal form, one factor at a time -/

/-- **The leading factor in palindromic normal form.**  Replacing it by its
normal form spells the same element with a conjugator no longer, so minimality
is untouched.  `GreendlingerWeight.exists_palindromic_isMinimalConjExpr` does
this for the two leading factors at once; the descent needs it for one, because
the second factor of one stage is the first factor of the next and must not be
renamed. -/
theorem exists_palindromic_head [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {x : FreeGroup α} {s : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((x, s) :: e) g) :
    ∃ c t : List (α × Bool), t ∈ symmetrization R ∧
      FreeGroup.IsReduced (palindrome c t) ∧
      IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g := by
  obtain ⟨hv, he, hlen, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨c, t, ht, hredt, heqt, hnormt⟩ := exists_palindrome_factor hR hRne h1 x
  refine ⟨c, t, ht, hredt, conjValid_cons_iff.mpr ⟨ht, h2⟩, ?_, ?_, ?_⟩
  · rw [conjEval_cons, heqt]
    rw [conjEval_cons] at he
    exact he
  · intro e₀ hv₀ he₀
    have hb := hlen e₀ hv₀ he₀
    simpa using hb
  · intro e₀ hv₀ he₀ hlen₀
    have hb : conjWeight ((FreeGroup.mk c, t) :: e) ≤ conjWeight ((x, s) :: e) := by
      simp only [conjWeight_cons]
      omega
    refine le_trans hb (hweight e₀ hv₀ he₀ ?_)
    simpa using hlen₀

/-- **The second factor in palindromic normal form**, with the first left
exactly as it is. -/
theorem exists_palindromic_snd [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {c t : List (α × Bool)} {x' : FreeGroup α} {s' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (x', s') :: e) g) :
    ∃ c' t' : List (α × Bool), t' ∈ symmetrization R ∧
      FreeGroup.IsReduced (palindrome c' t') ∧
      IsMinimalConjExpr R
        ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g := by
  obtain ⟨hv, he, hlen, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  obtain ⟨c', t', ht', hredt', heqt', hnormt'⟩ :=
    exists_palindrome_factor hR hRne h3 x'
  refine ⟨c', t', ht', hredt',
    conjValid_cons_iff.mpr ⟨h1, conjValid_cons_iff.mpr ⟨ht', h4⟩⟩, ?_, ?_, ?_⟩
  · rw [conjEval_cons, conjEval_cons, heqt']
    rw [conjEval_cons, conjEval_cons] at he
    exact he
  · intro e₀ hv₀ he₀
    have hb := hlen e₀ hv₀ he₀
    simpa using hb
  · intro e₀ hv₀ he₀ hlen₀
    have hb : conjWeight ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e)
        ≤ conjWeight ((FreeGroup.mk c, t) :: (x', s') :: e) := by
      simp only [conjWeight_cons]
      omega
    refine le_trans hb (hweight e₀ hv₀ he₀ ?_)
    simpa using hlen₀

/-! ## The leading cancellation, at any length -/

/-- **The descent's setup, for an expression of any length.**  The reduced word
splits as `P' ++ B'`: the leading palindrome loses the block `M` the product
destroys, and the reduced word of everything after it loses the matching prefix
`invRev M`.

`GreendlingerMinimal.exists_descent_decomposition` does this for the
propositional count; this version keeps the tail as data, which is what the
induction needs in order to hand the tail to itself. -/
theorem exists_leading_cancellation [DecidableEq α]
    {c t w : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    (hw : FreeGroup.IsReduced w)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (heval : conjEval ((FreeGroup.mk c, t) :: e) = FreeGroup.mk w) :
    ∃ P' M B' : List (α × Bool),
      palindrome c t = P' ++ M ∧
        (conjEval e).toWord = FreeGroup.invRev M ++ B' ∧
        w = P' ++ B' := by
  obtain ⟨P', M, B', h1, h2, h3, h4⟩ :=
    exists_cancellation_decomposition (conjEval e).toWord
      FreeGroup.isReduced_toWord (palindrome c t) hredp
  refine ⟨P', M, B', h1, h2, ?_⟩
  have hprod : FreeGroup.mk (palindrome c t) * FreeGroup.mk (conjEval e).toWord
      = FreeGroup.mk w := by
    rw [FreeGroup.mk_toWord, mk_palindrome, ← conjEval_cons]
    exact heval
  have h5 : FreeGroup.mk w = FreeGroup.mk (P' ++ B') := by
    rw [← hprod, h4]
  have h6 := FreeGroup.reduce.sound h5
  rwa [hw.reduce_eq, h3.reduce_eq] at h6

/-! ## Rerouting a conjugator that hugs a factor -/

/-- **The reroute identity.**  A conjugator of the form `c ++ y` may send its
`y` around the preceding factor instead of alongside it: the two factors swap,
and the conjugator of the one that moves picks up the whole rotation `t`. -/
theorem mk_palindrome_mul_reroute (c t y m : List (α × Bool)) :
    FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome (c ++ y) m)
      = FreeGroup.mk (palindrome (c ++ (t ++ y)) m)
        * FreeGroup.mk (palindrome c t) := by
  simp only [mk_palindrome, mk_append_mul]
  group

/-- **No conjugator hugs more than half of the factor it passes.**  If the next
conjugator runs backwards along the trailing part `E` of the rotation ---
`c' = c ++ (invRev E ++ Z)` with `t = t₀ ++ E` --- then rerouting it the other
way around that rotation replaces `invRev E` by `t₀`, at no other cost.  The
move is available in a minimal expression, so it cannot save anything:
`|E| ≤ |t₀|`, that is, `2|E| ≤ |t|`.

This is the fifth weight move, and it is the one that speaks to the case the
descent still owes.  It falls short of it by exactly the difference between
`2|E| ≤ |t|` and `2|E| < |t|`: a conjugator may hug precisely half a rotation,
and then the rotation contributes exactly half of itself, which is not more than
half. -/
theorem eaten_le_of_minimal_reroute [DecidableEq α] {R : Set (List (α × Bool))}
    {c t₀ E Z m : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t₀ ++ E)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m) :: e) g)
    (hred : FreeGroup.IsReduced (c ++ (FreeGroup.invRev E ++ Z)))
    (hredc : FreeGroup.IsReduced c) :
    E.length ≤ t₀.length := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  have hv2 : ConjValid R
      ((FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))), m)
        :: (FreeGroup.mk c, t₀ ++ E) :: e) :=
    conjValid_cons_iff.mpr ⟨h3, conjValid_cons_iff.mpr ⟨h1, h4⟩⟩
  have hmove := mk_palindrome_mul_reroute c (t₀ ++ E) (FreeGroup.invRev E ++ Z) m
  simp only [mk_palindrome] at hmove
  have he2 : conjEval
      ((FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))), m)
        :: (FreeGroup.mk c, t₀ ++ E) :: e) = g := by
    rw [← conjEval_replace_two hmove]
    exact he
  have hlen2 : ((FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))), m)
      :: (FreeGroup.mk c, t₀ ++ E) :: e).length
      = ((FreeGroup.mk c, t₀ ++ E)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnormc : FreeGroup.norm (FreeGroup.mk c) = c.length :=
    norm_mk_of_isReduced hredc
  have hnorm1 : FreeGroup.norm (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)))
      = c.length + (E.length + Z.length) := by
    rw [norm_mk_of_isReduced hred]
    simp [FreeGroup.invRev_length]
  have hcollapse : FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z)))
      = FreeGroup.mk (c ++ (t₀ ++ Z)) := by
    simp only [mk_append_mul, mk_invRev_eq_inv]
    group
  have hnorm2 : FreeGroup.norm
      (FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))))
      ≤ c.length + (t₀.length + Z.length) := by
    rw [hcollapse]
    have hb := norm_mk_le_length (c ++ (t₀ ++ Z))
    rw [List.length_append, List.length_append] at hb
    exact hb
  omega

/-- **The reroute identity, with the meeting point folded in.**  The next
conjugator overhangs by `y` and meets the next rotation in `v`.  Sending it
around the preceding factor the other way and rotating the next rotation past
`v` conjugates it by `c ++ invRev z`, where `z` is what the preceding rotation
has left beyond the meeting point. -/
theorem mk_palindrome_mul_reroute_meet (c y v z u : List (α × Bool)) :
    FreeGroup.mk (palindrome c (FreeGroup.invRev (y ++ (v ++ z))))
        * FreeGroup.mk (palindrome (c ++ y) (v ++ u))
      = FreeGroup.mk (palindrome (c ++ FreeGroup.invRev z) (u ++ v))
        * FreeGroup.mk (palindrome c (FreeGroup.invRev (y ++ (v ++ z)))) := by
  simp only [mk_palindrome, mk_append_mul, mk_invRev_eq_inv]
  group

/-- **The overhang is at most what lies beyond the meeting point.**  In the
configuration the descent's last case produces --- the second conjugator
overhangs the first by `y`, the two rotations meet in `v`, and the first
inverted rotation is `y ++ v ++ z` --- rerouting costs `|z|` and saves `|y|`, so
a minimal expression forces `|y| ≤ |z|`.

Both moves of this file are strictly better than the naive one, which would only
say `|y| ≤ |v| + |z|`: rotating the next relator past the meeting point pays the
`|v|` back. -/
theorem overhang_le_of_minimal_reroute_meet [DecidableEq α]
    {R : Set (List (α × Bool))} {c y v z u : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, FreeGroup.invRev (y ++ (v ++ z)))
        :: (FreeGroup.mk (c ++ y), v ++ u) :: e) g)
    (hred : FreeGroup.IsReduced (c ++ y)) : y.length ≤ z.length := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  have hswap : u ++ v ∈ symmetrization R := append_swap_mem_symmetrization h3
  have hv2 : ConjValid R
      ((FreeGroup.mk (c ++ FreeGroup.invRev z), u ++ v)
        :: (FreeGroup.mk c, FreeGroup.invRev (y ++ (v ++ z))) :: e) :=
    conjValid_cons_iff.mpr ⟨hswap, conjValid_cons_iff.mpr ⟨h1, h4⟩⟩
  have hmove := mk_palindrome_mul_reroute_meet c y v z u
  simp only [mk_palindrome] at hmove
  have he2 : conjEval
      ((FreeGroup.mk (c ++ FreeGroup.invRev z), u ++ v)
        :: (FreeGroup.mk c, FreeGroup.invRev (y ++ (v ++ z))) :: e) = g := by
    rw [← conjEval_replace_two hmove]
    exact he
  have hlen2 : ((FreeGroup.mk (c ++ FreeGroup.invRev z), u ++ v)
      :: (FreeGroup.mk c, FreeGroup.invRev (y ++ (v ++ z))) :: e).length
      = ((FreeGroup.mk c, FreeGroup.invRev (y ++ (v ++ z)))
        :: (FreeGroup.mk (c ++ y), v ++ u) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnorm : FreeGroup.norm (FreeGroup.mk (c ++ y)) = c.length + y.length := by
    rw [norm_mk_of_isReduced hred, List.length_append]
  have hnorm2 : FreeGroup.norm (FreeGroup.mk (c ++ FreeGroup.invRev z))
      ≤ c.length + z.length := by
    have hb := norm_mk_le_length (c ++ FreeGroup.invRev z)
    rw [List.length_append, FreeGroup.invRev_length] at hb
    exact hb
  omega

/-- **How close the two moves come.**  The block the leading factor loses to the
meeting eats `y ++ v` out of its rotation, and the rotation has `|y| + |v| + |z|`
letters; the move above gives `2|y| + |v| ≤ |t|`, where the descent's last case
needs `2(|y| + |v|) < |t|`.

The distance between the two is `|v|`, the meeting overlap, which `C'(1/6)`
bounds by a sixth of the rotation and no local move bounds by zero.  This is
the precise sense in which the remaining case is the classical count and not a
bookkeeping gap. -/
theorem two_mul_overhang_add_meet_le [DecidableEq α]
    {R : Set (List (α × Bool))} {c y v z u : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, FreeGroup.invRev (y ++ (v ++ z)))
        :: (FreeGroup.mk (c ++ y), v ++ u) :: e) g)
    (hred : FreeGroup.IsReduced (c ++ y)) :
    2 * y.length + v.length
      ≤ (FreeGroup.invRev (y ++ (v ++ z))).length := by
  have h := overhang_le_of_minimal_reroute_meet hmin hred
  rw [FreeGroup.invRev_length, List.length_append, List.length_append]
  omega

/-! ## The hug, bounded -/

/-- **The reroute identity, mirrored.**  When the *leading* conjugator runs along
the next rotation --- `c = c' ++ q` with `q` a prefix of `q ++ r = t'` --- the
leading factor may be sent around that rotation the other way instead: the two
factors swap and the leading one is re-conjugated by `c' ++ invRev r`.

This is the move `eaten_le_of_minimal_reroute` performs with the roles of the
two factors exchanged, and unlike that one it cannot be obtained from it by
`conjInv`, because inverting the expression reverses the whole list. -/
theorem mk_palindrome_mul_hug_reroute (c' q r t : List (α × Bool)) :
    FreeGroup.mk (palindrome (c' ++ q) t)
        * FreeGroup.mk (palindrome c' (q ++ r))
      = FreeGroup.mk (palindrome c' (q ++ r))
        * FreeGroup.mk (palindrome (c' ++ FreeGroup.invRev r) t) := by
  simp only [mk_palindrome, mk_append_mul, mk_invRev_eq_inv]
  group

/-- **No conjugator hugs more than half of the rotation it runs along.**  The
leading conjugator overhangs the next one by `q`, and `q` is a prefix of the next
rotation `q ++ r`; sending the leading factor the other way around that rotation
costs `|r|` and saves `|q|`, so a minimal expression forces `|q| ≤ |r|`, that is
`2|q| ≤ |t'|`.

This is the last unbounded quantity in the descent's analysis of what a leading
block eats: past the next conjugator the block meets only relator letters, which
`C'(1/6)` bounds by a sixth, and the stretch before that --- the hug --- is
bounded here by a half.  A half against the five twelfths the next factor keeps
is what still crosses, and that crossing is the whole of what
`LeadingConfinement` still carries. -/
theorem hug_le_of_minimal_reroute [DecidableEq α] {R : Set (List (α × Bool))}
    {c' q r t : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk (c' ++ q), t) :: (FreeGroup.mk c', q ++ r) :: e) g)
    (hred : FreeGroup.IsReduced (c' ++ q)) (hredc' : FreeGroup.IsReduced c') :
    q.length ≤ r.length := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  have hv2 : ConjValid R
      ((FreeGroup.mk c', q ++ r)
        :: (FreeGroup.mk (c' ++ FreeGroup.invRev r), t) :: e) :=
    conjValid_cons_iff.mpr ⟨h3, conjValid_cons_iff.mpr ⟨h1, h4⟩⟩
  have hmove := mk_palindrome_mul_hug_reroute c' q r t
  simp only [mk_palindrome] at hmove
  have he2 : conjEval
      ((FreeGroup.mk c', q ++ r)
        :: (FreeGroup.mk (c' ++ FreeGroup.invRev r), t) :: e) = g := by
    rw [← conjEval_replace_two hmove]
    exact he
  have hlen2 : ((FreeGroup.mk c', q ++ r)
      :: (FreeGroup.mk (c' ++ FreeGroup.invRev r), t) :: e).length
      = ((FreeGroup.mk (c' ++ q), t)
        :: (FreeGroup.mk c', q ++ r) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnorm : FreeGroup.norm (FreeGroup.mk (c' ++ q)) = c'.length + q.length := by
    rw [norm_mk_of_isReduced hred, List.length_append]
  have hnormc' : FreeGroup.norm (FreeGroup.mk c') = c'.length :=
    norm_mk_of_isReduced hredc'
  have hnorm2 : FreeGroup.norm (FreeGroup.mk (c' ++ FreeGroup.invRev r))
      ≤ c'.length + r.length := by
    have hb := norm_mk_le_length (c' ++ FreeGroup.invRev r)
    rw [List.length_append, FreeGroup.invRev_length] at hb
    exact hb
  omega

/-! ## The stem takes the short way round -/

/-- **The leading factor may be sent to the end.**  Conjugating it by everything
that follows moves it past the whole tail, at the same factor count, so a
minimal expression cannot prefer the shorter of the two routes: the leading
conjugator is no longer than the route around the rest of the product.

This is a sixth weight move, and unlike the reroutes it is *global* --- it
compares the stem against the whole tail rather than against one neighbour.  Its
useful form is the corollary below: when the leading conjugator is a prefix of
what the tail spells, as the descent's decomposition always makes it, the stem
is at most half of that word. -/
theorem norm_le_of_minimal_sendToEnd [DecidableEq α] {R : Set (List (α × Bool))}
    {x : FreeGroup α} {s : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((x, s) :: e) g) :
    FreeGroup.norm x ≤ FreeGroup.norm ((conjEval e)⁻¹ * x) := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  have hv2 : ConjValid R (e ++ [((conjEval e)⁻¹ * x, s)]) := by
    refine conjValid_append h2 ?_
    intro y hy
    rcases List.mem_singleton.mp hy with rfl
    exact h1
  have he2 : conjEval (e ++ [((conjEval e)⁻¹ * x, s)]) = g := by
    rw [conjEval_append, conjEval_cons, conjEval_nil, ← he, conjEval_cons]
    group
  have hlen2 : (e ++ [((conjEval e)⁻¹ * x, s)]).length = ((x, s) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  rw [conjWeight_append, conjWeight_cons, conjWeight_cons, conjWeight_nil] at hle
  omega

/-- **The leading factor may be sent past any initial stretch of the tail.**
Conjugating it by the product of the factors it passes keeps the factor count
and the element, so minimality compares the stem against every partial route,
not only the whole one.

`norm_le_of_minimal_sendToEnd` is the case `e₂ = []`, and the reroute moves are
the case where `e₁` is a single factor and the conjugator collapses; this is the
family they all live in. -/
theorem norm_le_of_minimal_sendPast [DecidableEq α] {R : Set (List (α × Bool))}
    {x : FreeGroup α} {s : List (α × Bool)}
    {e₁ e₂ : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((x, s) :: (e₁ ++ e₂)) g) :
    FreeGroup.norm x ≤ FreeGroup.norm ((conjEval e₁)⁻¹ * x) := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  have hv₁ : ConjValid R e₁ := fun y hy => h2 y (List.mem_append_left _ hy)
  have hv₂ : ConjValid R e₂ := fun y hy => h2 y (List.mem_append_right _ hy)
  have hv2 : ConjValid R (e₁ ++ (((conjEval e₁)⁻¹ * x, s) :: e₂)) :=
    conjValid_append hv₁ (conjValid_cons_iff.mpr ⟨h1, hv₂⟩)
  have he2 : conjEval (e₁ ++ (((conjEval e₁)⁻¹ * x, s) :: e₂)) = g := by
    rw [conjEval_append, conjEval_cons, ← he, conjEval_cons, conjEval_append]
    group
  have hlen2 : (e₁ ++ (((conjEval e₁)⁻¹ * x, s) :: e₂)).length
      = ((x, s) :: (e₁ ++ e₂)).length := by
    simp
    omega
  have hle := hweight _ hv2 he2 hlen2
  rw [conjWeight_append, conjWeight_cons, conjWeight_cons, conjWeight_append]
    at hle
  omega

/-- **The stem is at most half of what the tail spells.**  When the leading
conjugator is a prefix of the tail's reduced word --- which is what the leading
decomposition always produces --- sending the factor to the end costs the rest
of that word, so minimality gives `2|c| ≤ |W|`. -/
theorem two_mul_leading_conjugator_le [DecidableEq α]
    {R : Set (List (α × Bool))} {c s X : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, s) :: e) g)
    (hredc : FreeGroup.IsReduced c)
    (hW : (conjEval e).toWord = c ++ X) :
    2 * c.length ≤ (conjEval e).toWord.length := by
  have hmove := norm_le_of_minimal_sendToEnd hmin
  have hnormc : FreeGroup.norm (FreeGroup.mk c) = c.length :=
    norm_mk_of_isReduced hredc
  have hinv : (conjEval e)⁻¹ * FreeGroup.mk c
      = FreeGroup.mk (FreeGroup.invRev X) := by
    have h1 : conjEval e = FreeGroup.mk c * FreeGroup.mk X := by
      have hb : FreeGroup.mk ((conjEval e).toWord) = FreeGroup.mk (c ++ X) := by
        rw [hW]
      rw [FreeGroup.mk_toWord, mk_append_mul] at hb
      exact hb
    rw [h1, mk_invRev_eq_inv]
    group
  have hbound : FreeGroup.norm (FreeGroup.mk (FreeGroup.invRev X)) ≤ X.length := by
    have hb := norm_mk_le_length (FreeGroup.invRev X)
    rwa [FreeGroup.invRev_length] at hb
  have hlen : (conjEval e).toWord.length = c.length + X.length := by
    rw [hW, List.length_append]
  rw [hnormc, hinv] at hmove
  omega

/-! ## What the descent still asks -/

/-- **The one statement the descent still asks for.**  At the head of a minimal
expression whose leading cancellation reaches past its own trailing conjugator,
the block the leading factor loses is matched inside the *next* factor's
palindrome: no factor is consumed whole by the cancellation of the one before
it.

It mentions no pieces and it is not a small-cancellation hypothesis: it is one
prefix statement about the words the decomposition produces, in exactly the way
`GreendlingerMinimal.TwoFactorRegime` was before `GreendlingerRegime`
discharged it.  What it buys is the right to read the destroyed block against a
rotation at all, and every case of the descent below except the free one uses
it. -/
def LeadingConfinement [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c' t' P' M : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g →
    palindrome c t = P' ++ M →
    FreeGroup.invRev M
      <+: (conjEval ((FreeGroup.mk c', t') :: e)).toWord →
    c.length < M.length →
    FreeGroup.invRev M <+: palindrome c' t'

/-- **Confinement is a race between two quantities.**  If what the next factor
keeps at the front of the rest of the product is `c' ++ u` for a prefix `u` of
its rotation, and the block the leading factor loses is no longer, the block is
confined --- it is read against the next palindrome and nothing else.

So `LeadingConfinement` is exactly the statement that the block does not outrun
what the next factor keeps.  Both sides of that race are bounded by the descent:
every case above leaves more than five twelfths of a rotation standing
(`|M| - |c| ≤ (|t| + |v|)/2` in the meet case, `≤ |t|/2` in the buried one,
`< |t|/6` in the overlap one), and every case eats less than seven twelfths.
Five twelfths and seven twelfths meet exactly at `1`, and the difference between
them is the meeting piece, bounded by `C'(1/6)` and by nothing smaller.  The
race is therefore not decided by any local re-expression move: with `|t'| = 60`
the moves permit `|q| = 17`, `|p| = 9`, `|y₂| = 25`, `|v₂| = 9`, all four
inequalities hold, and the leading block consumes the whole surviving rotation
and runs past it.

And running past it is not absurd.  What the block runs into are letters of the
factors *after* the next one, which is what happens when two non-adjacent
factors contribute arcs that meet --- three mutually adjacent regions, say.  So
`LeadingConfinement` is not a consequence of planarity and should not be read as
one.

The race is decided, however, in the regime where the *next* conjugator is the
longer one: `eaten_lt_of_long_next_conjugator` proves confinement there outright
from the survival bound, because past `c'` the block meets only relator letters
and `C'(1/6)` bounds a piece by a sixth against five twelfths kept.  What is
still open is the hug: the leading conjugator running along the next rotation,
where the eaten part is not a piece and no local move bounds it below a half.

**Warning: this hypothesis is very likely false, and the theorems that assume it
should be read as a reduction, not as a usable gate.**  Here is a configuration
that satisfies every constraint the six weight moves and `C'(1/6)` impose while
violating confinement.  Take `|t₁| = |t₂| = 60`, `c₂ = []`, `c₁ = q` the first
`21` letters of `t₂`, the tail eating `|E₂| = 30` letters of `t₂` into `c₃`
(so `|M₂| = 30` and `c₃ = invRev E₂ ++ Z`), and the leading block eating
`q`, then a piece `p` of `9` letters, then `21` letters of `Z`.  Every
inequality holds --- `2|q| = 42 ≤ 60`, `6|p| = 54 < 60`, `2|E₂| = 60 ≤ 60`,
`|P₂| ≤ |P₁|`, `2|c₁| ≤ |W₂|` --- and the block runs `21` letters past what the
second factor keeps.

And the Greendlinger conclusion still holds there, but for a reason the descent
does not look at: the *third* factor's rotation is untouched, sitting in the
word at position `51`, exactly where the block stops.  So the descent's real
missing ingredient is not confinement at all --- it is a positional invariant
strong enough to say that the subword the tail carries lies beyond the leading
block, which the present invariant (position at least `|c| + j`, for `6j < |t|`)
is too weak to give when the tail's own conjugator is short. -/
theorem confinement_of_tail_survival {c' t' u M W : List (α × Bool)}
    (hW : FreeGroup.invRev M <+: W)
    (hsurv : c' ++ u <+: W)
    (hu : u <+: t')
    (hfit : M.length ≤ c'.length + u.length) :
    FreeGroup.invRev M <+: palindrome c' t' := by
  have hlen : (FreeGroup.invRev M).length ≤ (c' ++ u).length := by
    rw [FreeGroup.invRev_length, List.length_append]
    omega
  have hstep : FreeGroup.invRev M <+: c' ++ u :=
    List.prefix_of_prefix_length_le hW hsurv hlen
  refine hstep.trans ?_
  obtain ⟨r, hr⟩ := hu
  refine ⟨r ++ FreeGroup.invRev c', ?_⟩
  unfold palindrome
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc u, hr]

/-- **The block cannot outrun the next rotation when the next conjugator is the
longer one.**  Past `c'` the block is matched against letters of the leading
rotation, so what it eats there is a common prefix of the next rotation and a
rotation of the inverted leading one --- a piece.  `C'(1/6)` bounds it by a
sixth, while the next factor keeps more than five twelfths of its rotation
(`m` below); so the block stops inside what the next factor keeps, and stops
early enough that a subword beginning a sixth of the way into the next rotation
is untouched.

Both conclusions are exactly what the descent's inheritance step consumes.  This
is the half of confinement that is a theorem: it needs only that the next factor
keeps five twelfths, which every case of the descent delivers.  The other half
--- the leading conjugator the longer, hugging the next rotation itself --- is
what `LeadingConfinement` still carries. -/
theorem eaten_lt_of_long_next_conjugator {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' y E M W : List (α × Bool)} {m : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hE : E <:+ t)
    (hinvM : FreeGroup.invRev M = c ++ FreeGroup.invRev E)
    (hMW : FreeGroup.invRev M <+: W)
    (hsurv : c' ++ t'.take m <+: W)
    (hm : m ≤ t'.length) (hmbig : 5 * t'.length < 12 * m)
    (hcy : c ++ y = c')
    (hne : t' ≠ (FreeGroup.invRev t).rotate y.length) :
    6 * (M.length - c'.length) < t'.length ∧ M.length ≤ c'.length + m := by
  have hMl : (FreeGroup.invRev M).length = M.length := FreeGroup.invRev_length
  have hmpos : 0 < m := by omega
  have ht'pos : 0 < t'.length := by omega
  rcases le_or_gt M.length c'.length with hshort | hlong
  · exact ⟨by omega, by omega⟩
  · set d : ℕ := min (M.length - c'.length) m with hd
    have hdm : d ≤ m := by omega
    have hdlen : (t'.take d).length = d := by
      rw [List.length_take]
      omega
    have htake : t'.take d <+: t'.take m := by
      have hb := List.take_prefix d (t'.take m)
      rwa [List.take_take, Nat.min_eq_left hdm] at hb
    have hpre : c' ++ t'.take d <+: FreeGroup.invRev M := by
      refine List.prefix_of_prefix_length_le
        (((List.prefix_append_right_inj c').mpr htake).trans hsurv) hMW ?_
      rw [List.length_append, hdlen, hMl]
      omega
    have hsplit : y ++ t'.take d <+: FreeGroup.invRev E := by
      refine (List.prefix_append_right_inj c).mp ?_
      rw [← List.append_assoc, hcy, ← hinvM]
      exact hpre
    have hrot : t'.take d <+: (FreeGroup.invRev t).rotate y.length :=
      prefix_rotate_of_append_prefix (hsplit.trans (invRev_prefix_of_suffix hE))
    have hpiece : IsPiece (symmetrization R) (t'.take d) :=
      isPiece_of_prefix_two ht'
        (rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length) hne
        (List.take_prefix _ _) hrot
    have h6 := six_mul_length_lt_of_isPiece hmetric hpiece ht' (List.take_prefix _ _)
    rw [hdlen] at h6
    exact ⟨by omega, by omega⟩

/-! ## No two factors cancel, adjacent or not -/

/-- **Minimality of the factor count forbids cancellation between *any* two
factors**, not only neighbours: if the leading factor is inverse to a later one
conjugated to it, the two can be deleted together --- conjugating the factors
between them by the leading one keeps them conjugates of symmetrized relators
and leaves an expression with two factors fewer.

`GreendlingerMinimal.IsMinimalConjExpr.mul_ne_one` is the neighbouring case.
This is the form a counting argument needs, since it is what says two factors
never describe the same region twice. -/
theorem conj_ne_inv_of_minimal [DecidableEq α] {R : Set (List (α × Bool))}
    {x y : FreeGroup α} {s s' : List (α × Bool)}
    {e₁ e₂ : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((x, s) :: (e₁ ++ ((y, s') :: e₂))) g) :
    x * FreeGroup.mk s * x⁻¹
        * (conjEval e₁ * (y * FreeGroup.mk s' * y⁻¹) * (conjEval e₁)⁻¹) ≠ 1 := by
  intro hcon
  obtain ⟨hv, he, hlen, -⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  have hv₁ : ConjValid R e₁ := fun z hz => h2 z (List.mem_append_left _ hz)
  have hv₂ : ConjValid R e₂ := fun z hz =>
    h2 z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
  have hval : ConjValid R (e₁ ++ e₂) := conjValid_append hv₁ hv₂
  have hx : x * FreeGroup.mk s * x⁻¹
      = conjEval e₁ * (y * FreeGroup.mk s' * y⁻¹)⁻¹ * (conjEval e₁)⁻¹ := by
    have h := mul_eq_one_iff_eq_inv.mp hcon
    rw [h]
    group
  have heval : conjEval (e₁ ++ e₂) = g := by
    rw [← he, conjEval_cons, conjEval_append, hx]
    rw [conjEval_append, conjEval_cons]
    group
  have hb := hlen (e₁ ++ e₂) hval heval
  simp only [List.length_cons, List.length_append] at hb
  omega

/-! ## The obligation in its right form -/

/-- **What the descent actually needs.**  Not that the leading block stops
inside the next factor's palindrome --- that is `LeadingConfinement`, and the
configuration in the header violates it --- but that the subword the rest of the
product carries lies *beyond* the block, together with the bound that the block
leaves the leading rotation partly standing.

In the header's configuration this holds while confinement fails: the block runs
21 letters past what the second factor keeps, and the third factor's rotation
sits exactly where the block stops.  So this, and not confinement, is the
statement a continuation should try to discharge. -/
def TailSubwordBeyondBlock [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c' t' P' M : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g →
    palindrome c t = P' ++ M →
    FreeGroup.invRev M
      <+: (conjEval ((FreeGroup.mk c', t') :: e)).toWord →
    c.length < M.length →
    M.length ≤ c.length + t.length ∧
      GreendlingerAt R M.length
        (conjEval ((FreeGroup.mk c', t') :: e)).toWord

/-- **The gate, from the obligation in its right form.**  No induction is
needed: either the block stays inside the trailing conjugator, and the whole
leading rotation survives, or the hypothesis hands over a subword of the rest of
the product lying beyond the block, which `greendlingerAt_inherit` carries into
the word.

This supersedes `greendlingerConclusion_of_leadingConfinement`, whose hypothesis
is probably false and whose statement is therefore probably vacuous. -/
theorem greendlinger_of_tailSubwordBeyondBlock [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hreg : TailSubwordBeyondBlock R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {e : List (FreeGroup α × List (α × Bool))}
    (hmin : IsMinimalConjExpr R e (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  cases e with
  | nil =>
      exfalso
      have hb := hmin.2.1
      rw [conjEval_nil] at hb
      have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
        rw [← FreeGroup.one_eq_mk]
        exact hb.symm
      have h2 := FreeGroup.reduce.sound h1
      rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
      exact hwne h2
  | cons x e' =>
      cases e' with
      | nil =>
          obtain ⟨x₁, s₁⟩ := x
          obtain ⟨c, t, ht, hredp, hmin'⟩ := exists_palindromic_head hR hRne hmin
          have htpos : 0 < t.length :=
            List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin'.2.1
          have hnil : FreeGroup.invRev M ++ B' = [] := by
            rw [← hgw, conjEval_nil]
            exact FreeGroup.toWord_eq_nil_iff.mpr rfl
          have hlen := congrArg List.length hnil
          rw [List.length_append, FreeGroup.invRev_length,
            List.length_nil] at hlen
          refine greendlinger_of_greendlingerAt (n := c.length + 0) ?_
          rw [hwe]
          exact greendlingerAt_of_short_cancellation ht heq (by omega) (by omega)
      | cons y e'' =>
          obtain ⟨x₁, s₁⟩ := x
          obtain ⟨x₂, s₂⟩ := y
          obtain ⟨c, t, c', t', ht, ht', hredp, hredp', hmin₂⟩ :=
            exists_palindromic_isMinimalConjExpr hR hRne hmin
          have htpos : 0 < t.length :=
            List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin₂.2.1
          have hcl : (FreeGroup.invRev c).length = c.length :=
            FreeGroup.invRev_length
          refine greendlinger_of_greendlingerAt (n := c.length + 0) ?_
          rw [hwe]
          rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
          · exact greendlingerAt_of_short_cancellation ht heq hshort (by omega)
          · obtain ⟨hhigh, hsub⟩ :=
              hreg c t c' t' P' M e'' (FreeGroup.mk w) hmin₂ heq ⟨B', hgw.symm⟩
                (by omega)
            exact greendlingerAt_inherit (n := M.length) heq hgw (by omega)
              le_rfl hsub

/-! ## The descent, at every length -/

/-- **The descent.**  For a minimal expression of *any* length whose leading
factor is in palindromic normal form, the reduced word contains more than half
of a symmetrized relator, beginning at or after position `|c| + j` for every
offset `j` below a sixth of the leading rotation.

The induction is on the expression, one factor at a time, through the four cases
of the leading cancellation.  Two of them inherit the tail's subword, and they
are where the slack is spent: the block eats at most `|v|` letters off the front
of what the tail spells, `v` is a piece of the tail's leading rotation, so
`6|v| < |t'|` and the tail's subword carried at offset `|v|` is untouched.  The
two weight moves of this file supply the position arithmetic: a block buried in
the next conjugator eats at most half the rotation, and a block meeting the next
rotation leaves at least the overhang standing.

Nothing here is special to two or three factors --- the same four cases run at
every length, which is what carries the descent past the two-factor barrier. -/
theorem greendlingerAt_of_isMinimalConjExpr [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hconf : LeadingConfinement R) :
    ∀ (e : List (FreeGroup α × List (α × Bool)))
      (c t w : List (α × Bool)) (j : ℕ),
      FreeGroup.IsReduced w → t ∈ symmetrization R →
        FreeGroup.IsReduced (palindrome c t) →
        IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) (FreeGroup.mk w) →
        6 * j < t.length →
        GreendlingerAt R (c.length + j) w := by
  intro e
  induction e with
  | nil =>
      intro c t w j hw ht hredp hmin hj
      obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
        exists_leading_cancellation hw hredp hmin.2.1
      have hnil : FreeGroup.invRev M ++ B' = [] := by
        rw [← hgw, conjEval_nil]
        exact FreeGroup.toWord_eq_nil_iff.mpr rfl
      have hlen := congrArg List.length hnil
      rw [List.length_append, FreeGroup.invRev_length, List.length_nil] at hlen
      rw [hwe]
      exact greendlingerAt_of_short_cancellation ht heq (by omega) hj
  | cons x e'' ih =>
      intro c t w j hw ht hredp hmin hj
      obtain ⟨x', s'⟩ := x
      obtain ⟨c', t', ht', hredp', hmin'⟩ := exists_palindromic_snd hR hRne hmin
      obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
        exists_leading_cancellation hw hredp hmin'.2.1
      have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
      have hpre : FreeGroup.invRev M
          <+: (conjEval ((FreeGroup.mk c', t') :: e'')).toWord := ⟨B', hgw.symm⟩
      have hmin₂ : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: e'')
          (FreeGroup.mk (conjEval ((FreeGroup.mk c', t') :: e'')).toWord) := by
        rw [FreeGroup.mk_toWord]
        exact hmin'.tail
      have ht'pos : 0 < t'.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht')
      have hredc : FreeGroup.IsReduced c :=
        isReduced_of_infix ⟨[], t ++ FreeGroup.invRev c, by simp [palindrome]⟩
          hredp
      have hredc' : FreeGroup.IsReduced c' :=
        isReduced_of_infix ⟨[], t' ++ FreeGroup.invRev c', by simp [palindrome]⟩
          hredp'
      rw [hwe]
      rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
      · exact greendlingerAt_of_short_cancellation ht heq hshort hj
      · have hconfp : FreeGroup.invRev M <+: palindrome c' t' :=
          hconf c t c' t' P' M e'' (FreeGroup.mk w) hmin' heq hpre (by omega)
        obtain ⟨B'', heq'⟩ := hconfp
        have hhigh : M.length ≤ c.length + t.length :=
          swallow_bound_of_minimal hRne hmetric hmin' ht ht' hredp hredp' heq
            heq'.symm
        have hb2 : M.length ≤ c'.length + t'.length :=
          swallow_bound_of_minimal' hRne hmetric hmin'.leadingPair ht ht' hredp
            hredp' heq heq'.symm
        have hcoin := mk_palindrome_mul_ne_one_of_minimal hmin'
        rcases le_or_gt c'.length c.length with hle | hgt
        · exact greendlingerAt_of_overlap hmetric ht ht' heq ⟨B'', heq'⟩
            (by omega) hle (by omega) hcoin hj
        · obtain ⟨E, hM, hEct⟩ := eaten_split ⟨P', heq.symm⟩ hlong.le
          have hEt : E <:+ t := eaten_suffix_of_le hM hEct (by omega)
          have hElen : M.length = E.length + c.length := by
            rw [hM, List.length_append, FreeGroup.invRev_length]
          have hinvM : FreeGroup.invRev M = c ++ FreeGroup.invRev E :=
            invRev_eaten_block hM
          have hEpre : c ++ FreeGroup.invRev E <+: palindrome c' t' := by
            rw [← hinvM]
            exact ⟨B'', heq'⟩
          have hP2 : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
            unfold palindrome
            rw [List.append_assoc]
          have hc'pre : c' <+: palindrome c' t' := by
            rw [hP2]
            exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
          have hcpre : c <+: palindrome c' t' :=
            (show c <+: c ++ FreeGroup.invRev E from ⟨_, rfl⟩).trans hEpre
          obtain ⟨y, hy⟩ := List.prefix_of_prefix_length_le hcpre hc'pre hgt.le
          have hylen : c'.length = c.length + y.length := by
            rw [← hy, List.length_append]
          rcases le_or_gt M.length c'.length with hin | hout
          · -- the block's image is buried in the second conjugator
            obtain ⟨Z, hZ⟩ := List.prefix_of_prefix_length_le
              (show FreeGroup.invRev M <+: palindrome c' t' from ⟨B'', heq'⟩)
              hc'pre (by rw [FreeGroup.invRev_length]; omega)
            have hc'eq : c' = c ++ (FreeGroup.invRev E ++ Z) := by
              rw [← hZ, hinvM, List.append_assoc]
            obtain ⟨t₀, ht₀⟩ := hEt
            have htlen : t₀.length + E.length = t.length := by
              rw [← ht₀, List.length_append]
            have hreroute : E.length ≤ t₀.length := by
              refine eaten_le_of_minimal_reroute (R := R) (c := c) (t₀ := t₀)
                (E := E) (Z := Z) (m := t') (e := e'') (g := FreeGroup.mk w)
                ?_ ?_ hredc
              · rw [ht₀, ← hc'eq]
                exact hmin'
              · rw [← hc'eq]
                exact hredc'
            have hIH := ih c' t'
              (conjEval ((FreeGroup.mk c', t') :: e'')).toWord 0
              FreeGroup.isReduced_toWord ht' hredp' hmin₂ (by omega)
            exact greendlingerAt_inherit (n := c'.length + 0) heq hgw (by omega)
              (by omega) hIH
          · -- the block reaches past the second conjugator, meeting its rotation
            have hEstep : FreeGroup.invRev E
                <+: y ++ (t' ++ FreeGroup.invRev c') := by
              refine (List.prefix_append_right_inj c).mp ?_
              rw [← List.append_assoc, hy, ← hP2]
              exact hEpre
            have hEinvlen : (FreeGroup.invRev E).length = E.length :=
              FreeGroup.invRev_length
            have hyE : y <+: FreeGroup.invRev E := by
              refine List.prefix_of_prefix_length_le
                (show y <+: y ++ (t' ++ FreeGroup.invRev c') from ⟨_, rfl⟩)
                hEstep ?_
              omega
            obtain ⟨v, hv⟩ := hyE
            have hvlen : y.length + v.length = E.length := by
              have hb := congrArg List.length hv
              rw [List.length_append, FreeGroup.invRev_length] at hb
              omega
            have hvstep : v <+: t' ++ FreeGroup.invRev c' := by
              refine (List.prefix_append_right_inj y).mp ?_
              rw [hv]
              exact hEstep
            have hvt' : v <+: t' :=
              List.prefix_of_prefix_length_le hvstep
                (show t' <+: t' ++ FreeGroup.invRev c' from ⟨_, rfl⟩) (by omega)
            have hyvinv : y ++ v <+: FreeGroup.invRev t := by
              rw [hv]
              exact invRev_prefix_of_suffix hEt
            obtain ⟨z, hz⟩ := hyvinv
            have hzlen : y.length + v.length + z.length = t.length := by
              have hb := congrArg List.length hz
              rw [List.length_append, List.length_append,
                FreeGroup.invRev_length] at hb
              omega
            have hvrot : v <+: (FreeGroup.invRev t).rotate y.length :=
              prefix_rotate_of_append_prefix ⟨z, hz⟩
            have hypre : y <+: FreeGroup.invRev t :=
              (show y <+: y ++ v from ⟨v, rfl⟩).trans ⟨z, hz⟩
            have hrotmem : (FreeGroup.invRev t).rotate y.length
                ∈ symmetrization R :=
              rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length
            by_cases hsame : t' = (FreeGroup.invRev t).rotate y.length
            · exact absurd
                (mk_palindrome_mul_eq_one_of_coincidence' hy.symm hypre hsame)
                hcoin
            · have hpiece : IsPiece (symmetrization R) v :=
                isPiece_of_prefix_two ht' hrotmem hsame hvt' hvrot
              have h6t' := six_mul_length_lt_of_isPiece hmetric hpiece ht' hvt'
              have h6t := six_mul_length_lt_of_isPiece hmetric hpiece hrotmem hvrot
              rw [List.length_rotate, FreeGroup.invRev_length] at h6t
              obtain ⟨u, hu⟩ := hvt'
              have htinv : FreeGroup.invRev (y ++ (v ++ z)) = t := by
                rw [← List.append_assoc, hz, FreeGroup.invRev_invRev]
              have hmeet : y.length ≤ z.length := by
                refine overhang_le_of_minimal_reroute_meet (R := R) (c := c)
                  (y := y) (v := v) (z := z) (u := u) (e := e'')
                  (g := FreeGroup.mk w) ?_ ?_
                · rw [htinv, hu, hy]
                  exact hmin'
                · rw [hy]
                  exact hredc'
              have hIH := ih c' t'
                (conjEval ((FreeGroup.mk c', t') :: e'')).toWord v.length
                FreeGroup.isReduced_toWord ht' hredp' hmin₂ (by omega)
              exact greendlingerAt_inherit (n := c'.length + v.length) heq hgw
                (by omega) (by omega) hIH

/-! ## The gate -/

/-- **The Greendlinger conclusion from a minimal expression of any length.** -/
theorem greendlinger_of_isMinimalConjExpr [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hconf : LeadingConfinement R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {e : List (FreeGroup α × List (α × Bool))}
    (hmin : IsMinimalConjExpr R e (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  cases e with
  | nil =>
      exfalso
      have hb := hmin.2.1
      rw [conjEval_nil] at hb
      have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
        rw [← FreeGroup.one_eq_mk]
        exact hb.symm
      have h2 := FreeGroup.reduce.sound h1
      rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
      exact hwne h2
  | cons x e'' =>
      obtain ⟨x₁, s₁⟩ := x
      obtain ⟨c, t, ht, hredp, hmin'⟩ := exists_palindromic_head hR hRne hmin
      have htpos : 0 < t.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
      exact greendlinger_of_greendlingerAt
        (greendlingerAt_of_isMinimalConjExpr hR hRne hmetric hconf e'' c t w 0 hw
          ht hredp hmin' (by omega))

/-- **Three or more factors.**  This is the hypothesis
`GreendlingerInduction.greendlingerConclusion_of_three_factor` asks for, and it
holds for every length at once: the descent never counts factors, it walks
them. -/
theorem greendlinger_of_three_or_more [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hconf : LeadingConfinement R)
    (w : List (α × Bool)) (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    (n : ℕ) (_hn : 3 ≤ n) (hmin : IsMinimalConjProduct R n (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hmin.1
  obtain ⟨e, hmine⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  exact greendlinger_of_isMinimalConjExpr hR hRne hmetric hconf hw hwne hmine

/-- **The gate, for a `C'(1/6)` family whose factors are never consumed whole.**
Every nonempty reduced word in the normal closure contains more than half of a
symmetrized relator --- at every number of factors, with the one- and two-factor
cases already unconditional and the longer ones supplied by the descent. -/
theorem greendlingerConclusion_of_leadingConfinement [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hconf : LeadingConfinement R) :
    GreendlingerConclusion R := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  exact greendlinger_of_isMinimalConjExpr hR hRne hmetric hconf hw hwne hmin

end SmallCancellationRouter
end GroupApproximation
