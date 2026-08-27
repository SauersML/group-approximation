import GroupApproximation.Sofic.GreendlingerCoincidence
import GroupApproximation.Sofic.GreendlingerMinimal
import GroupApproximation.Sofic.GreendlingerSharpLandingAux

/-!
# The minimal-expression layer, twinned where it actually carries a constant

The eight modules that hold the minimal-expression and coincidence machinery
--- `GreendlingerExpression`, `GreendlingerNormalForm`,
`GreendlingerReducedness`, `GreendlingerMirror`, `GreendlingerMinimal`,
`GreendlingerMaxConjugator`, `GreendlingerCoincidence` and
`GreendlingerDeepestMatch` --- are overwhelmingly `λ`-neutral.  Palindromic
normal form, reducedness, the duality under the formal inverse, products of
conjugates, the normal-closure identification, minimality of the factor count
and the selection of a maximising conjugator all name no ratio whatever, so
they are already the statements the sharp lane needs and no twin of them can
exist.  What does carry a constant is a short list, and this file supplies the
twins on it that were still missing.

## What was already twinned, and is not repeated here

`GreendlingerMaxConjugator`'s arithmetic is twinned in full inside
`GreendlingerSharpTwins`: `keeps_of_two_pieces` by `two_pieces_budget`,
`keeps_of_three_pieces` by `three_pieces_budget`, `survivor_gt_half` by
`survivor_gt_sharp`, `no_overrun_of_hug_and_piece` by
`no_overrun_of_hug_and_piece_sharp`, `not_second_overrun` by
`not_second_overrun_sharp`, `MaximalJunction` by `MaximalJunctionSharp` (both
demoted, for the same reason), and `greendlingerAt_of_maximalJunction` by
`greendlingerAtSharp_of_maximalJunctionSharp`.  Its remaining inequality,
`not_overrun_into_conjugator`, names no ratio at all --- it plays a cover bound
against a meet bound and a conjugator domination --- so it serves both towers as
written.

`GreendlingerDeepestMatch.six_mul_intrusion_lt` is twinned by
`GreendlingerSharpTwins.intrusion_lt_of_metric`, and
`landsIn_of_conjugatorAbsorbed` by `landsInSharp_of_conjugatorAbsorbed`.

## What is proved here

Four things, in three groups.

**The duality, at the sharp bound.**  `greendlingerSharp_of_invRev` is the twin
of `GreendlingerMirror.greendlinger_of_invRev`, and it transports verbatim:
`invRev` and `rotate` preserve length, so `(1 − 3λ)·|s| < |u|` survives the
mirror exactly as `|s| < 2|u|` does.  On top of it the two mirrored descent
theorems, `greendlingerSharp_of_short_cancellation_mirror` and
`greendlingerSharp_of_two_palindromes_mirror`, are instances of the sharp
located producers `greendlingerAtSharp_of_short_cancellation` and
`greendlingerAtSharp_of_overlap` at the exchanged factors, read at offset `0`.

The zero offset is what `0 < lam` buys, exactly as in
`greendlingerSharp_of_cascadeLandingSharp`: the located producers ask for
`j < λ·|t|`, and `j = 0` needs `0 < λ·|t|`.  The `λ`-free versions needed no
such hypothesis because `6 * 0 < |t|` is free.

**The one-relator base, at the sharp bound.**  `greendlingerSharp_of_isConj`
and `greendlingerSharp_of_isConjProduct_one` twin
`GreendlingerOneRelator.greendlinger_of_isConj` and
`GreendlingerExpression.greendlinger_of_isConjProduct_one`.  A conjugate of a
relator carries a *whole* rotation, so the bound to check is
`(1 − 3λ)·|t| < |t|`, which is `0 < 3λ·|t|` --- again `0 < lam` and a nonempty
relator, and nothing else.  `two_le_of_isMinimalConjProductSharp` and the two
descent theorems above it follow.

**The head length conjunct of the `i_c = 0` cascade branch.**
`GreendlingerSharpTwins.cascadeLandingSharp_of_conjugatorAbsorbedSite` takes
`M.length + j ≤ c.length + t.length` as a *hypothesis*, where the `λ`-free
`GreendlingerDeepestMatch.cascadeLanding_of_conjugatorAbsorbed` derives it from
the two piece bounds by `omega`.  `add_le_of_two_lam_bounds` is that derivation
at a general constant --- two losses each under `λ·T` fit inside `T` as soon as
`λ ≤ 1/2` --- and `cascadeLandingSharp_of_conjugatorAbsorbed` is the branch with
the conjunct proved rather than assumed.  `λ ≤ 1/2` is free in range and is the
only place the bound is read; at `λ = 1/6` the same step was two sixths against
a whole, absorbed by `omega`.

## What this does not do

Nothing here discharges an open residual.  The descent theorems twinned in §3
run through `IsMinimalConjProduct`, the factor-count minimand, and
`GreendlingerMinimal` records that `GreendlingerRegime` supersedes that route
with `greendlinger_of_isMinimalConjExpr_two`; the live lane runs through
`IsMinimalConjExpr` and `CascadeLandingSharp`.  They are twinned so that the two
towers stay comparable statement for statement, not because the sharp gate goes
through them.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The duality, at the sharp bound -/

/-- **The sharp Greendlinger conclusion is invariant under the formal
inverse.**  The `λ`-twin of `GreendlingerMirror.greendlinger_of_invRev`, and the
same proof: `invRev` turns the contiguous subword into a contiguous subword of
the inverse and the prefix of a relator into a suffix of one, a suffix is a
prefix of the rotation bringing it to the front, and `symmetrization` contains
that rotation.

Neither `invRev` nor `rotate` changes a length, so the arc bound crosses the
mirror untouched --- which is why this needs no constant hypothesis at all, and
why the whole duality layer of `GreendlingerMirror` is `λ`-neutral apart from
the two theorems that quote a producer. -/
theorem greendlingerSharp_of_invRev {R : Set (List (α × Bool))} {lam : ℚ}
    {w : List (α × Bool)}
    (h : ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: FreeGroup.invRev w ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  obtain ⟨s, hs, u, huinf, hupre, hlt⟩ := h
  have hinf : FreeGroup.invRev u <:+: w := by
    have h1 := invRev_infix_of_infix huinf
    rwa [FreeGroup.invRev_invRev] at h1
  have hsuf : FreeGroup.invRev u <:+ FreeGroup.invRev s :=
    invRev_suffix_of_prefix hupre
  refine ⟨(FreeGroup.invRev s).rotate
      ((FreeGroup.invRev s).length - (FreeGroup.invRev u).length),
    rotate_mem_symmetrization (invRev_mem_symmetrization hs) _,
    FreeGroup.invRev u, hinf, prefix_rotate_of_suffix hsuf, ?_⟩
  rw [List.length_rotate, FreeGroup.invRev_length, FreeGroup.invRev_length]
  exact hlt

/-- **The mirror of the free case, at the sharp bound.**  The `λ`-twin of
`GreendlingerMirror.greendlinger_of_short_cancellation_mirror`: a cancellation
confined to the *second* factor's leading conjugator leaves the second rotation
whole, and a whole rotation beats `(1 − 3λ)` of itself as soon as `0 < λ`.

The mirrored configuration is handed to
`GreendlingerSharpTwins.greendlingerAtSharp_of_short_cancellation` at offset
`0`, and `greendlingerSharp_of_invRev` transports the conclusion back. -/
theorem greendlingerSharp_of_short_cancellation_mirror
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6) (hRne : ∀ r ∈ R, r ≠ [])
    {c' t' P' M B' : List (α × Bool)}
    (ht' : t' ∈ symmetrization R)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hlen : M.length ≤ c'.length) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  refine greendlingerSharp_of_invRev ?_
  rw [FreeGroup.invRev_append]
  have hm1 : palindrome c' (FreeGroup.invRev t')
      = FreeGroup.invRev B' ++ M := by
    rw [← invRev_palindrome, heq', FreeGroup.invRev_append,
      FreeGroup.invRev_invRev]
  have ht'' : FreeGroup.invRev t' ∈ symmetrization R :=
    invRev_mem_symmetrization ht'
  have htpos : 0 < (FreeGroup.invRev t').length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht'')
  have hcl : (FreeGroup.invRev c').length = c'.length := FreeGroup.invRev_length
  exact greendlingerSharp_of_greendlingerAtSharp
    (greendlingerAtSharp_of_short_cancellation (B' := FreeGroup.invRev P')
      hlam ht'' hm1 (by omega) (cast_zero_lt_lam_mul hlam0 htpos))

/-- **The two-factor descent read backwards, at the sharp bound.**  The `λ`-twin
of `GreendlingerMirror.greendlinger_of_two_palindromes_mirror`.

The duality is `λ`-free and is quoted unchanged: the mirrored cancellation is a
cancellation of the same shape with the two factors exchanged and the same
destroyed block, so the case that was open --- the *second* conjugator the
longer --- is an instance of the sharp overlap producer
`GreendlingerSharpLandingAux.greendlingerAtSharp_of_overlap` at the exchanged
factors.  `hcoin` is again what minimality of the expression supplies. -/
theorem greendlingerSharp_of_two_palindromes_mirror
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M B' : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hhigh : M.length ≤ (FreeGroup.invRev c').length + t'.length)
    (hle : c.length ≤ c'.length)
    (hfit : c'.length - c.length + M.length ≤ c'.length + t.length)
    (hcoin : FreeGroup.mk (palindrome c t)
      * FreeGroup.mk (palindrome c' t') ≠ 1) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  refine greendlingerSharp_of_invRev ?_
  rw [FreeGroup.invRev_append]
  -- the mirrored cancellation, with the two factors exchanged
  have hm1 : palindrome c' (FreeGroup.invRev t')
      = FreeGroup.invRev B' ++ M := by
    rw [← invRev_palindrome, heq', FreeGroup.invRev_append,
      FreeGroup.invRev_invRev]
  have hm2 : palindrome c (FreeGroup.invRev t)
      = FreeGroup.invRev M ++ FreeGroup.invRev P' := by
    rw [← invRev_palindrome, heq, FreeGroup.invRev_append]
  have hm3 : FreeGroup.invRev M <+: palindrome c (FreeGroup.invRev t) := by
    rw [hm2]
    exact ⟨FreeGroup.invRev P', rfl⟩
  have htl : (FreeGroup.invRev t).length = t.length := FreeGroup.invRev_length
  have htl' : (FreeGroup.invRev t').length = t'.length := FreeGroup.invRev_length
  have hcoin' : FreeGroup.mk (palindrome c' (FreeGroup.invRev t'))
      * FreeGroup.mk (palindrome c (FreeGroup.invRev t)) ≠ 1 := by
    rw [mk_palindrome_invRev, mk_palindrome_invRev]
    intro hcon
    refine hcoin ?_
    rw [← inv_inv (FreeGroup.mk (palindrome c t)
      * FreeGroup.mk (palindrome c' t')), mul_inv_rev, hcon, inv_one]
  have ht'' : FreeGroup.invRev t' ∈ symmetrization R :=
    invRev_mem_symmetrization ht'
  have htpos : 0 < (FreeGroup.invRev t').length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht'')
  exact greendlingerSharp_of_greendlingerAtSharp
    (greendlingerAtSharp_of_overlap (B' := FreeGroup.invRev P') hlam hmetric
      ht'' (invRev_mem_symmetrization ht) hm1 hm3 (by omega) hle (by omega)
      hcoin' (cast_zero_lt_lam_mul hlam0 htpos))

/-! ## 2.  The one-relator base, at the sharp bound -/

/-- **A conjugate of a relator carries a whole rotation.**  The `λ`-twin of
`GreendlingerOneRelator.greendlinger_of_isConj`.

The geometry is `λ`-free and is quoted verbatim: the palindromic normal form
spells the conjugate by a reduced palindrome, so the reduced word *is* that
palindrome and the rotation sits inside it uncancelled.  What moves is only the
last line.  The `λ`-free file finished with `|t| < 2|t|`, which needs the
rotation nonempty; the sharp bound asks `(1 − 3λ)·|t| < |t|`, which needs the
rotation nonempty *and* `0 < λ`. -/
theorem greendlingerSharp_of_isConj [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {s : List (α × Bool)} (hs : s ∈ symmetrization R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hconj : IsConj (FreeGroup.mk s) (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧
        (1 - 3 * lam) * (t.length : ℚ) < (u.length : ℚ) := by
  have hscyc : FreeGroup.IsCyclicallyReduced s :=
    symmetrization_isCyclicallyReduced hR hs
  have hsne : s ≠ [] := ne_nil_of_mem_symmetrization hRne hs
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨L, hL⟩ : ∃ L, FreeGroup.mk L = g := ⟨g.toWord, FreeGroup.mk_toWord⟩
  obtain ⟨c, k, hpred, hpeq⟩ := exists_conjugation_normalForm hscyc hsne L
  -- the conjugate is spelled by a reduced palindrome, so it *is* `w`
  have hmk : FreeGroup.mk w = FreeGroup.mk (palindrome c (s.rotate k)) := by
    rw [← hg, ← hL, hpeq]
  have hwe : w = palindrome c (s.rotate k) := by
    have h1 := FreeGroup.reduce.sound hmk
    rwa [hw.reduce_eq, hpred.reduce_eq] at h1
  refine ⟨s.rotate k, rotate_mem_symmetrization hs k, s.rotate k, ?_,
    List.prefix_refl _, ?_⟩
  · rw [hwe]
    exact ⟨c, FreeGroup.invRev c, rfl⟩
  · have hlen : 0 < (s.rotate k).length := by
      rw [List.length_rotate]
      exact List.length_pos_iff.mpr hsne
    have hq : (0 : ℚ) < ((s.rotate k).length : ℚ) := by exact_mod_cast hlen
    linarith [mul_pos hlam0 hq]

/-- **The base of the descent, at the sharp bound.**  The `λ`-twin of
`GreendlingerExpression.greendlinger_of_isConjProduct_one`: an expression with a
single conjugate factor already gives the sharp conclusion. -/
theorem greendlingerSharp_of_isConjProduct_one [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (h : IsConjProduct R 1 (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧
        (1 - 3 * lam) * (t.length : ℚ) < (u.length : ℚ) := by
  obtain ⟨c, s, hs, h', hh', heq⟩ := h
  have hh1 : h' = 1 := hh'
  subst hh1
  refine greendlingerSharp_of_isConj hlam0 hR hRne hs hw ?_
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [heq]
  group

/-! ## 3.  The two-factor descent, at the sharp bound -/

/-- **The count the sharp descent starts from.**  The `λ`-twin of
`GreendlingerMinimal.two_le_of_isMinimalConjProduct`: if the sharp conclusion
fails for a nonempty reduced word, its shortest expression has at least two
factors.  Zero is impossible for a nonempty reduced word --- that clause is
`λ`-free --- and one is the sharp one-relator case just proved. -/
theorem two_le_of_isMinimalConjProductSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {n : ℕ} (hmin : IsMinimalConjProduct R n (FreeGroup.mk w))
    (hno : ¬ ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧
        (1 - 3 * lam) * (t.length : ℚ) < (u.length : ℚ)) : 2 ≤ n := by
  obtain ⟨hn, -⟩ := hmin
  rcases n with _ | _ | n
  · exact absurd hn (not_isConjProduct_zero hw hwne)
  · exact absurd (greendlingerSharp_of_isConjProduct_one hlam0 hR hRne hw hn) hno
  · omega

/-- **The two-factor case of the sharp gate.**  The `λ`-twin of
`GreendlingerMinimal.greendlinger_of_isMinimalConjProduct_two`.

Every structural step is quoted from the `λ`-free proof, because every
structural step is `λ`-neutral: the descent decomposition, the palindromic form
of the single trailing factor, the non-cancellation `hcoin` that minimality
supplies, and `regime_cases` splitting on which conjugator is the longer.  Only
the three producers move --- to `greendlingerAtSharp_of_short_cancellation`, to
`greendlingerAtSharp_of_overlap`, and to the mirror above --- and each is read at
offset `0`, which is what `0 < lam` pays for.

`TwoFactorRegime` is unchanged: it is a pure length statement about the
cancellation and names no constant, so the sharp twin consumes the very same
predicate. -/
theorem greendlingerSharp_of_isMinimalConjProduct_two [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hmin : IsMinimalConjProduct R 2 (FreeGroup.mk w))
    (hregime : TwoFactorRegime R w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
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
  -- the zero offset the sharp located producers ask for
  have htpos : 0 < t.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
  rw [hwe]
  rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
  · exact greendlingerSharp_of_greendlingerAtSharp
      (greendlingerAtSharp_of_short_cancellation hlam ht heq hshort
        (cast_zero_lt_lam_mul hlam0 htpos))
  · rcases le_or_gt M.length c'.length with hshort' | hlong'
    · exact greendlingerSharp_of_short_cancellation_mirror hlam0 hlam hRne ht'
        heq' hshort'
    · obtain ⟨hb1, hb2⟩ := hregime c t c' t' P' M B' ht ht' heq heq' hwe
      rcases regime_cases hb1 hb2 with
        ⟨hhigh, hle, hfit⟩ | ⟨hhigh, hle, hfit⟩
      · exact greendlingerSharp_of_greendlingerAtSharp
          (greendlingerAtSharp_of_overlap hlam hmetric ht ht' heq hpre hhigh hle
            hfit hcoin (cast_zero_lt_lam_mul hlam0 htpos))
      · exact greendlingerSharp_of_two_palindromes_mirror hlam0 hlam hRne hmetric
          ht ht' heq heq' hhigh hle hfit hcoin

/-- **The sharp gate for everything the two-factor descent reaches.**  The
`λ`-twin of `GreendlingerMinimal.greendlinger_of_isMinimalConjProduct_le_two`:
none is impossible, one is the sharp one-relator case, and two is the descent
just closed. -/
theorem greendlingerSharp_of_isMinimalConjProduct_le_two [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {n : ℕ} (hn : n ≤ 2) (hmin : IsMinimalConjProduct R n (FreeGroup.mk w))
    (hregime : TwoFactorRegime R w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  rcases n with _ | _ | n
  · exact absurd hmin.1 (not_isConjProduct_zero hw hwne)
  · exact greendlingerSharp_of_isConjProduct_one hlam0 hR hRne hw hmin.1
  · have hn0 : n = 0 := by omega
    subst hn0
    exact greendlingerSharp_of_isMinimalConjProduct_two hlam0 hlam hR hRne
      hmetric hw hmin hregime

/-! ## 4.  The head length conjunct of the `i_c = 0` cascade branch -/

/-- **Two `λ`-losses fit inside one rotation.**  As soon as `λ ≤ 1/2`, two
quantities each strictly under `λ·T` sum to at most `T`.

This is the sharp reading of the step the `λ`-free
`GreendlingerDeepestMatch.cascadeLanding_of_conjugatorAbsorbed` performs inside
`omega`: there the two losses are each under a sixth, so their sum is under a
third and the fit is invisible.  Stated rationally the branch has to be named,
and `λ ≤ 1/2` is what names it --- free in the `λ ≤ 1/6` band the whole sharp
lane lives in. -/
theorem add_le_of_two_lam_bounds {lam : ℚ} (hlam : lam ≤ 1 / 2) {a b T : ℕ}
    (ha : (a : ℚ) < lam * (T : ℚ)) (hb : (b : ℚ) < lam * (T : ℚ)) :
    a + b ≤ T := by
  have hT : (0 : ℚ) ≤ (T : ℚ) := by exact_mod_cast Nat.zero_le T
  have hhalf : lam * (T : ℚ) ≤ 1 / 2 * (T : ℚ) :=
    mul_le_mul_of_nonneg_right hlam hT
  have hsum : ((a + b : ℕ) : ℚ) < (T : ℚ) := by
    push_cast
    linarith
  exact_mod_cast hsum.le

/-- **`CascadeLandingSharp` on the `i_c = 0` branch, with the head conjunct
proved.**  The `λ`-twin of
`GreendlingerDeepestMatch.cascadeLanding_of_conjugatorAbsorbed`.

`GreendlingerSharpTwins.cascadeLandingSharp_of_conjugatorAbsorbedSite` reaches
the same disjunct but *assumes* `M.length + j ≤ c.length + t.length`.  Here it
is derived, exactly as the `λ`-free file derives it: the orientation lemma
places the eaten segment `E` inside the head rotation, `intrusion_lt_of_metric`
bounds it and the surviving stretch `j` each by `λ·|t|`, and
`add_le_of_two_lam_bounds` fits the two inside `|t|`.

The orientation, the segment identification and the landing itself are all
`λ`-free and are quoted rather than replayed. -/
theorem cascadeLandingSharp_of_conjugatorAbsorbed [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 2)
    (hmetric : MetricSmallCancellation R lam)
    {c t t' c' E A M P' B' : List (α × Bool)} {k N j : ℕ}
    {e f : List (FreeGroup α × List (α × Bool))}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length)
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hM : M = E ++ FreeGroup.invRev c)
    (hintr : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k)
    (hf : f.length < e.length)
    (hV : (conjEval e).toWord
      = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin' : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)))
    (hN : N ≤ c'.length + E.length)
    (hfit : M.length + N ≤ A.length + c'.length + E.length) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') ∨
      (M.length + j ≤ c.length + t.length ∧
        LandsInSharp R lam M.length (conjEval e).toWord e.length) := by
  -- the orientation lemma identifies the segment `E` the caller named, and
  -- places it inside the rotation
  have hEt : E <:+ t := by
    obtain ⟨E', hM', -, hE't, -, -⟩ := eaten_prefix_orientation heq hlow hhigh
    have hEE : E = E' := List.append_cancel_right (hM.symm.trans hM')
    rw [hEE]
    exact hE't
  have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
  have hMlen : M.length = E.length + (FreeGroup.invRev c).length := by
    rw [hM, List.length_append]
  have hbound := (intrusion_lt_of_metric hmetric ht ht' hEt hintr hne).1
  have hsum : E.length + j ≤ t.length := add_le_of_two_lam_bounds hlam hbound hj
  refine Or.inr ⟨by omega, ?_⟩
  exact landsInSharp_of_conjugatorAbsorbed hmetric ht ht' hEt hintr hne hf hV
    hredp' hmin' hN hfit

/-- **The same, with the coincidence discharged from minimality.**  The `λ`-twin
of `GreendlingerCoincidence.cascadeLanding_of_conjugatorAbsorbed'`.

The distinctness hypothesis is replaced by the data that produces it --- the
landing factor's position in the tail, the minimality of the whole expression,
and the overhang of the head conjugator past the effective conjugator --- and
`invRev_ne_rotate_of_minimal`, which supplies it, names no constant and is
quoted unchanged.  So the entire coincidence layer of `GreendlingerCoincidence`
is `λ`-neutral, and this is the only statement in that file that needed a
twin. -/
theorem cascadeLandingSharp_of_conjugatorAbsorbed' [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 2)
    (hmetric : MetricSmallCancellation R lam)
    {c t t' c' d q E A M P' B' : List (α × Bool)} {N j : ℕ}
    {e e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length)
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hM : M = E ++ FreeGroup.invRev c)
    (hintr : FreeGroup.invRev E <+: t'.rotate q.length)
    (he : e = e₁ ++ ((FreeGroup.mk c', t') :: f))
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hd : FreeGroup.mk d = conjEval e₁ * FreeGroup.mk c')
    (hcq : c = d ++ q) (hq : q <+: t')
    (hf : f.length < e.length)
    (hV : (conjEval e).toWord
      = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin' : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)))
    (hN : N ≤ c'.length + E.length)
    (hfit : M.length + N ≤ A.length + c'.length + E.length) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') ∨
      (M.length + j ≤ c.length + t.length ∧
        LandsInSharp R lam M.length (conjEval e).toWord e.length) := by
  subst he
  exact cascadeLandingSharp_of_conjugatorAbsorbed hlam hmetric ht ht' heq hlow
    hhigh hj hM hintr (invRev_ne_rotate_of_minimal hmin hd hcq hq) hf hV hredp'
    hmin' hN hfit

end SmallCancellationRouter
end GroupApproximation
