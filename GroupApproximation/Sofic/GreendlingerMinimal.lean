import GroupApproximation.Sofic.GreendlingerMirror

/-!
# Shortest expressions, and the two-factor descent

`GreendlingerExpression` turned "an element of the normal closure" into "a
product of `n` conjugates of symmetrized relators", so that the remaining layer
of the gate became an induction on `n`.  The induction runs on a **shortest**
expression, and this file makes that word mean something and then spends it.

## Minimality as an object

`IsMinimalConjProduct R n g` says `g` has an expression with `n` factors and
none with fewer.  Every element of the normal closure has one
(`exists_isMinimalConjProduct`, by well-ordering of `ℕ`), and for a nonempty
reduced word the count is at least two unless the gate's conclusion already
holds (`two_le_of_isMinimalConjProduct`): `n = 0` is impossible and `n = 1` is
`GreendlingerOneRelator`.

## What minimality buys

Exactly one thing: `IsMinimalConjProduct.mul_ne_one` --- **two adjacent factors
of a shortest expression do not cancel.**  Were their product trivial, deleting
both would express the same element with two factors fewer.

That single fact is what the descent needed.  `GreendlingerOverlap` shows the
converse of the missing step: if the overlap a cancellation eats lands in the
very relator it was eaten out of, then the two palindromes spell mutually
inverse elements.  So in a shortest expression the two relators are distinct
words, the overlap is a piece, and `C'(1/6)` applies.  Nothing about pieces is
assumed anywhere, and `GreendlingerMirror` supplies the same conclusion when the
two conjugators are ordered the other way.

## The descent's setup

`exists_descent_decomposition` assembles, for an expression with at least one
factor, everything the two preceding files consume:

* the leading factor in palindromic normal form
  (`exists_conjugation_normalForm`), so it is spelled by a reduced
  `palindrome c t` with `t` a symmetrized relator;
* the rest of the product spelled by its own reduced word;
* the cancellation decomposition of the two
  (`exists_cancellation_decomposition`);
* the identification of the result with the given reduced word `w`, because
  reduced words spelling the same element are equal.

For two factors the rest of the product is a single conjugate, so its reduced
word is again a palindrome (`exists_palindrome_of_isConjProduct_one`), and
`greendlinger_of_isMinimalConjProduct_two` closes that case outright.  What it
still asks of the caller is not a piece and not a distinctness, but the *length
regime*: that the cancellation neither eats past the first rotation into its
leading conjugator nor runs past the second rotation into its trailing one.
Those are the two cases in which the product destroys a whole factor, and they
are the remaining frontier of the descent.

The regime is two inequalities, one per factor, and `regime_cases` splits them
by which conjugator is the longer: whichever way that goes, `GreendlingerOverlap`
or its mirror `GreendlingerMirror` applies, so the ordering itself is never an
assumption.  `GreendlingerRegime` discharges the inequalities themselves, from
minimality of the total *conjugator length* --- a second minimand the factor
count cannot see --- and supersedes the theorem below with an unconditional one
(`greendlinger_of_isMinimalConjExpr_two`).

Unconditional; the `C'(1/6)` hypothesis enters only in the last statement, and
only through `greendlinger_of_two_palindromes`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Shortest expressions -/

/-- `g` has an expression with `n` conjugate factors and none with fewer. -/
def IsMinimalConjProduct (R : Set (List (α × Bool))) (n : ℕ) (g : FreeGroup α) :
    Prop :=
  IsConjProduct R n g ∧ ∀ m, m < n → ¬ IsConjProduct R m g

/-- **Every expressible element has a shortest expression**, by well-ordering of
`ℕ`.  This is what makes "minimal expression" a legitimate object of the
induction rather than an informal phrase. -/
theorem exists_isMinimalConjProduct {R : Set (List (α × Bool))} {g : FreeGroup α}
    (h : ∃ n, IsConjProduct R n g) : ∃ n, IsMinimalConjProduct R n g := by
  classical
  exact ⟨Nat.find h, And.intro (Nat.find_spec h) fun _m hm => Nat.find_min h hm⟩

/-- The same, keyed to membership in the normal closure. -/
theorem exists_isMinimalConjProduct_of_mem_normalClosure
    (R : Set (List (α × Bool))) (g : FreeGroup α)
    (hg : g ∈ Subgroup.normalClosure (FreeGroup.mk '' R)) :
    ∃ n, IsMinimalConjProduct R n g :=
  exists_isMinimalConjProduct ((mem_normalClosure_iff R g).mp hg)

/-! ## What minimality buys -/

/-- **Minimality, spent.**  Two adjacent factors of a shortest expression do not
cancel: if they did, deleting both would express the same element with two
factors fewer.

This is the only consequence of the minimal *count*, and it is the whole of what
the descent needs from it. -/
theorem IsMinimalConjProduct.mul_ne_one {R : Set (List (α × Bool))} {n : ℕ}
    {a b g : FreeGroup α} (hmin : IsMinimalConjProduct R (n + 2) (a * (b * g)))
    (hg : IsConjProduct R n g) : a * b ≠ 1 := by
  intro hone
  obtain ⟨-, hshort⟩ := hmin
  refine hshort n (by omega) ?_
  have hcollapse : a * (b * g) = g := by
    rw [← mul_assoc, hone, one_mul]
  rw [hcollapse]
  exact hg

/-- The same, read on the two leading palindromes of the descent: the
cancellation between them cannot destroy them both. -/
theorem mk_palindrome_mul_ne_one {R : Set (List (α × Bool))} {n : ℕ}
    {c t c' t' : List (α × Bool)} {g G : FreeGroup α}
    (hmin : IsMinimalConjProduct R (n + 2) G)
    (hG : G = FreeGroup.mk (palindrome c t)
      * (FreeGroup.mk (palindrome c' t') * g))
    (hg : IsConjProduct R n g) :
    FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') ≠ 1 := by
  subst hG
  exact IsMinimalConjProduct.mul_ne_one hmin hg

/-- A product that is not the identity is not spelled by the empty word, so the
reduced word the descent works with is nonempty. -/
theorem residue_ne_nil {P' B' : List (α × Bool)}
    (h : FreeGroup.mk (P' ++ B') ≠ 1) : P' ++ B' ≠ [] := by
  intro hnil
  refine h ?_
  rw [hnil, ← FreeGroup.one_eq_mk]

/-! ## The base of the induction, counted -/

/-- A shortest expression of a nonempty reduced word has at least one factor. -/
theorem one_le_of_isMinimalConjProduct [DecidableEq α] {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {n : ℕ} (hmin : IsMinimalConjProduct R n (FreeGroup.mk w)) : 1 ≤ n := by
  obtain ⟨hn, -⟩ := hmin
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd hn (not_isConjProduct_zero hw hwne)
  · exact hpos

/-- **The count the descent starts from.**  If the Greendlinger conclusion fails
for a nonempty reduced word, its shortest expression has at least two factors:
zero is impossible, and one is the one-relator case. -/
theorem two_le_of_isMinimalConjProduct [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {n : ℕ} (hmin : IsMinimalConjProduct R n (FreeGroup.mk w))
    (hno : ¬ ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧ t.length < 2 * u.length) : 2 ≤ n := by
  obtain ⟨hn, -⟩ := hmin
  rcases n with _ | _ | n
  · exact absurd hn (not_isConjProduct_zero hw hwne)
  · exact absurd (greendlinger_of_isConjProduct_one hR hRne hw hn) hno
  · omega

/-! ## The descent's setup -/

/-- A single conjugate factor is spelled by a reduced palindrome, so its reduced
word *is* that palindrome. -/
theorem exists_palindrome_of_isConjProduct_one [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {g : FreeGroup α} (h : IsConjProduct R 1 g) :
    ∃ c t : List (α × Bool), t ∈ symmetrization R ∧ g.toWord = palindrome c t := by
  obtain ⟨x, s, hs, g', hg', heq⟩ := h
  have hg1 : g' = 1 := hg'
  subst hg1
  obtain ⟨c, k, hred, hnf⟩ := exists_conjugation_normalForm
    (symmetrization_isCyclicallyReduced hR hs)
    (ne_nil_of_mem_symmetrization hRne hs) x.toWord
  rw [FreeGroup.mk_toWord] at hnf
  refine ⟨c, s.rotate k, rotate_mem_symmetrization hs k, ?_⟩
  have hgeq : g = FreeGroup.mk (palindrome c (s.rotate k)) := by
    rw [heq, mul_one, hnf]
  rw [hgeq, FreeGroup.toWord_mk, hred.reduce_eq]

/-- **The descent's setup.**  A reduced word spelling an expression with at
least one factor splits as `P' ++ B'`: the leading factor, in palindromic normal
form, loses the block `M` the product destroys, and the rest of the product
loses the matching prefix `invRev M`.

Everything `GreendlingerDescent` and `GreendlingerOverlap` consume is produced
here, out of the normal form and the cancellation decomposition and nothing
else. -/
theorem exists_descent_decomposition [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) {n : ℕ}
    (h : IsConjProduct R (n + 1) (FreeGroup.mk w)) :
    ∃ (c t P' M B' : List (α × Bool)) (g : FreeGroup α),
      t ∈ symmetrization R ∧
        FreeGroup.IsReduced (palindrome c t) ∧
        palindrome c t = P' ++ M ∧
        IsConjProduct R n g ∧
        FreeGroup.mk w = FreeGroup.mk (palindrome c t) * g ∧
        g.toWord = FreeGroup.invRev M ++ B' ∧
        w = P' ++ B' := by
  obtain ⟨x, s, hs, g, hg, heq⟩ := h
  obtain ⟨c, k, hred, hnf⟩ := exists_conjugation_normalForm
    (symmetrization_isCyclicallyReduced hR hs)
    (ne_nil_of_mem_symmetrization hRne hs) x.toWord
  rw [FreeGroup.mk_toWord] at hnf
  have hprod : FreeGroup.mk w
      = FreeGroup.mk (palindrome c (s.rotate k)) * g := by
    rw [heq, hnf]
  have hprod' : FreeGroup.mk w
      = FreeGroup.mk (palindrome c (s.rotate k)) * FreeGroup.mk g.toWord := by
    rw [hprod, FreeGroup.mk_toWord]
  obtain ⟨P', M, B', h1, h2, h3, h4⟩ :=
    exists_cancellation_decomposition g.toWord FreeGroup.isReduced_toWord
      (palindrome c (s.rotate k)) hred
  refine ⟨c, s.rotate k, P', M, B', g, rotate_mem_symmetrization hs k, hred, h1,
    hg, hprod, h2, ?_⟩
  have h5 : FreeGroup.mk w = FreeGroup.mk (P' ++ B') := by
    rw [hprod', h4]
  have h6 := FreeGroup.reduce.sound h5
  rwa [hw.reduce_eq, h3.reduce_eq] at h6

/-- **The one input the two-factor descent still asks for**, in its simplest
form: for the decomposition the descent produces, the destroyed block does not
swallow either rotation whole.

Nothing else is owed.  Both clauses are pure length statements about the
cancellation --- no piece, no distinctness, no small-cancellation hypothesis is
hidden in either --- and `regime_cases` turns them into the conjugator-ordering
disjunction the two geometric theorems consume. -/
def TwoFactorRegime (R : Set (List (α × Bool))) (w : List (α × Bool)) : Prop :=
  ∀ c t c' t' P' M B' : List (α × Bool),
    t ∈ symmetrization R → t' ∈ symmetrization R →
    palindrome c t = P' ++ M →
    palindrome c' t' = FreeGroup.invRev M ++ B' →
    w = P' ++ B' →
    M.length ≤ c.length + t.length ∧ M.length ≤ c'.length + t'.length

/-- The regime, split by which conjugator is the longer.  Whichever way the two
compare, the corresponding geometric theorem applies: this is the only place the
ordering is mentioned, and it is not an assumption. -/
theorem regime_cases {c t c' t' M : List (α × Bool)}
    (h1 : M.length ≤ c.length + t.length) (h2 : M.length ≤ c'.length + t'.length) :
    (M.length ≤ (FreeGroup.invRev c).length + t.length ∧
        c'.length ≤ c.length ∧
        c.length - c'.length + M.length ≤ c.length + t'.length) ∨
      (M.length ≤ (FreeGroup.invRev c').length + t'.length ∧
        c.length ≤ c'.length ∧
        c'.length - c.length + M.length ≤ c'.length + t.length) := by
  have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
  have hcl' : (FreeGroup.invRev c').length = c'.length := FreeGroup.invRev_length
  rcases le_or_gt c'.length c.length with hle | hlt
  · exact Or.inl ⟨by omega, hle, by omega⟩
  · exact Or.inr ⟨by omega, by omega, by omega⟩

/-- **The two-factor case of the gate, closed.**  An element whose shortest
expression has two factors satisfies the Greendlinger conclusion.

Nothing about pieces is assumed and no distinctness is assumed: minimality
supplies both, through `mk_palindrome_mul_ne_one` and the coincidence
computation of `GreendlingerOverlap`.  What is still asked of the caller is the
*length regime* --- that the cancellation stays inside the two rotations --- and
that is the remaining frontier of the descent, not a small-cancellation
hypothesis in disguise.  It is asked only in the case that survives both free
cases: the cancellation reaches past *both* conjugators.

`GreendlingerRegime.greendlinger_of_isMinimalConjExpr_two` is this theorem with
the regime proved rather than assumed, at the price of asking for an expression
minimal in conjugator length as well as in factor count. -/
theorem greendlinger_of_isMinimalConjProduct_two [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hmin : IsMinimalConjProduct R 2 (FreeGroup.mk w))
    (hregime : TwoFactorRegime R w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  obtain ⟨c, t, P', M, B', g, ht, -, heq, hg, hprod, hgw, hwe⟩ :=
    exists_descent_decomposition hR hRne hw hmin.1
  obtain ⟨c', t', ht', hgt⟩ := exists_palindrome_of_isConjProduct_one hR hRne hg
  have hgm : g = FreeGroup.mk (palindrome c' t') := by
    rw [← hgt, FreeGroup.mk_toWord]
  have heq' : palindrome c' t' = FreeGroup.invRev M ++ B' := by
    rw [← hgt]
    exact hgw
  have hpre : FreeGroup.invRev M <+: palindrome c' t' := by
    rw [heq']
    exact ⟨B', rfl⟩
  have hcoin : FreeGroup.mk (palindrome c t)
      * FreeGroup.mk (palindrome c' t') ≠ 1 := by
    refine mk_palindrome_mul_ne_one hmin ?_
      (show IsConjProduct R 0 (1 : FreeGroup α) from rfl)
    rw [hprod, hgm, mul_one]
  rw [hwe]
  rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
  · exact greendlinger_of_short_cancellation hRne ht heq hshort
  · rcases le_or_gt M.length c'.length with hshort' | hlong'
    · exact greendlinger_of_short_cancellation_mirror hRne ht' heq' hshort'
    · obtain ⟨hb1, hb2⟩ := hregime c t c' t' P' M B' ht ht' heq heq' hwe
      rcases regime_cases hb1 hb2 with
        ⟨hhigh, hle, hfit⟩ | ⟨hhigh, hle, hfit⟩
      · exact greendlinger_of_two_palindromes hRne hmetric ht ht' heq hpre hhigh
          hle hfit hcoin
      · exact greendlinger_of_two_palindromes_mirror hRne hmetric ht ht' heq
          heq' hhigh hle hfit hcoin

/-- **The gate, for everything the descent reaches.**  A `C'(1/6)` family
satisfies the Greendlinger conclusion for every nonempty reduced word whose
shortest expression has at most two conjugate factors: none is impossible, one
is the one-relator case, and two is the descent just closed.

What separates this from `GreendlingerGate` itself is the induction on longer
expressions --- and, inside the two-factor case, the length regime.  Nothing
else is outstanding. -/
theorem greendlinger_of_isMinimalConjProduct_le_two [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {n : ℕ} (hn : n ≤ 2) (hmin : IsMinimalConjProduct R n (FreeGroup.mk w))
    (hregime : TwoFactorRegime R w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  rcases n with _ | _ | n
  · exact absurd hmin.1 (not_isConjProduct_zero hw hwne)
  · exact greendlinger_of_isConjProduct_one hR hRne hw hmin.1
  · have hn0 : n = 0 := by omega
    subst hn0
    exact greendlinger_of_isMinimalConjProduct_two hR hRne hmetric hw hmin
      hregime

end SmallCancellationRouter
end GroupApproximation
