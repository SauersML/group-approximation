import GroupApproximation.Sofic.GreendlingerRegime
import GroupApproximation.Sofic.GreendlingerTwoPieceRegime
import GroupApproximation.Sofic.GreendlingerBeyond
import GroupApproximation.Sofic.GreendlingerSharpTwins
import GroupApproximation.Sofic.GreendlingerSharpChunks
import GroupApproximation.Sofic.GreendlingerSharpRigidity

/-!
# The regime layer at an arbitrary constant

`GreendlingerRegime`, `GreendlingerTwoPieceRegime` and `GreendlingerBeyond`
decide *which regime* a configuration is in by comparing lengths against a
fraction, and each of them writes that fraction as a sixth or as a half.  This
file states the same splits at an arbitrary `λ`.

Three of the four layers the regime rests on turn out to carry no constant at
all, so nothing here twins them:

* `GreendlingerCancellation` is the cancellation decomposition of a product of
  two reduced words --- a fact about free groups, with no piece and no fraction
  in sight;
* `GreendlingerSlide` is five identities between products of palindromes, each
  proved by `group`;
* `GreendlingerWeight` is the weight bookkeeping, whose `2` in
  `overhang_le_of_minimal` and whose `1` in `overhang_le_of_minimal_meet` are
  *savings* of a shortening move and not fractions of a relator ---
  `GreendlingerSharpChunks` already records this, and §3 there states the
  arithmetic of the collisions those bounds enter;
* `GreendlingerCombinatorics` is letters, rotation and symmetrization closure.

`GreendlingerMinimal.regime_cases` is likewise constant-free: it splits on which
conjugator is longer, which is an ordering of two natural numbers and not a
comparison against a fraction.

What *is* pinned to a constant is the following, and it is what this file moves.

## 1.  The swallow bound

`swallow_bound_of_minimal_of_prefix` spends `C'(1/6)` four times, in four
branches, and each spend is one of the three collisions
`GreendlingerSharpChunks` §3 already states rationally:

| branch | `λ`-free step | sharp step | costs |
| --- | --- | --- | --- |
| rotations meet, second conjugator shorter | `6\|p\| < \|t'\|` against `\|q\| ≤ 2\|p\|` | `not_overhang_of_slide_sharp` | `λ ≤ 1/3` |
| second rotation covers the first inverted | `6\|t\| < \|t\|` | `not_isPiece_self_sharp` | `λ ≤ 1` |
| rotations meet, second conjugator longer | `6\|v\| < \|t\|` against `\|y\| ≤ \|v\|` | `not_overhang_of_meet_sharp` | `λ ≤ 1/2` |
| first inverted rotation covers the second | `6\|t'\| < \|t'\|` | `not_isPiece_self_sharp` | `λ ≤ 1` |

So the whole bound costs `λ ≤ 1/3`, twice the band the lane runs in.  The other
two branches are absorb moves, which read no constant at all.

**The `λ`-free statement is weaker than its proof.**  Transcribing it revealed
that `heq`, `M`, `P'` and the contradiction hypothesis are never used: the six
branches derive `False` from the prefix `c ++ invRev t <+: palindrome c' t'`
alone, and the length bound is then read off by `False.elim`.  So the core
below is stated as what is actually proved --- that adjacent palindrome cannot
begin with the leading conjugator followed by the inverted leading rotation ---
and the two bound-shaped twins are corollaries of it.  The `λ`-free file states
only the corollaries; nothing there is wrong, but the strength was invisible.

## 2.  The block-search trichotomy

`GreendlingerBeyond.blockStop_cases` splits on `2(k + (b - |c'|)) < |t'|`: the
factor a block arrives at either keeps more than half of its rotation beyond the
block, or is overrun, or stops inside having kept at most half.  That half is
the *conclusion*'s constant, `1 - 3λ` at `λ = 1/6`, not the piece bound, so the
sharp split is against the budget `3λ|t'|` --- exactly the budget
`GreendlingerSharpTwins.greendlingerAtSharp_of_bounded_cancellation` consumes.
`SubwordBeyondSharp` and its three moves are then the `λ`-free predicate and
moves verbatim: transport and composition never read the bound.

## 3.  The two-piece long-overhang branch

`twoPiece_of_long_overhang` reads the same half twice --- once as
`|t'| < 2|q|`, the hypothesis that puts both pieces in `P'`, and once in each
conjunct of `TwoPieceConclusion`.  Both become `1 - 3λ`, and the eaten suffix
costs one piece out of the budget of three, so the twin needs no band at all:
`hmetric` alone suffices.

The warning in `GreendlingerTwoPieceRegime` carries over unchanged --- the
complementary band is where `GreendlingerTwoPiece` is *false*, and stating the
conclusion sharply does not make it true there.  What the twin buys is that the
branch which *is* provable no longer forces the constant.

Nothing here is new mathematics; it is the `λ = 1/6` evaluation undone.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The swallow bound at an arbitrary constant -/

/-- **The adjacent palindrome cannot begin with the conjugator and the inverted
rotation**, at any `λ ≤ 1/3`.  The sharp core of
`GreendlingerRegime.swallow_bound_of_minimal_of_prefix`, and --- as the module
docstring records --- the whole of what that theorem's proof establishes.

Six branches, exhaustive on how the two conjugators and the two rotations
compare:

* the whole inverted rotation sits inside the second conjugator --- **absorb**,
  saving `|t|`, and no constant is read;
* the second conjugator is the shorter, and
  - the whole `t'` sits inside the first conjugator --- **absorb**, saving
    `|t'|`;
  - `t'` meets `invRev t` in `p` --- **slide**, and `not_overhang_of_slide_sharp`
    collides the piece bound on `p` with the weight bound `|q| ≤ 2|p|`;
  - `t'` covers `invRev t` --- then `invRev t` is a piece of itself, which
    `not_isPiece_self_sharp` forbids;
* the second conjugator is the longer, and
  - `t'` meets `invRev t` in `v` --- **meet**, and `not_overhang_of_meet_sharp`
    collides the piece bound on `v` with `|y| ≤ |v|`;
  - `invRev t` covers `t'` --- then `t'` is a piece of itself.

Every branch that is not a weight contradiction ends at a *coincidence*, where
the two factors are mutually inverse and the factor count closes it.  So both
minimalities are spent, each on exactly the cases the other cannot reach, and
that division is independent of `λ`.

Nonemptiness of the relators is still asked for, because the two absorb moves
save `|t'|` and `|t|` and a saving of zero is no saving.  The four branches that
read the constant no longer need it: at `λ ≤ 1/3` the rational collisions close
on the empty rotation too. -/
theorem not_adjacent_prefix_of_minimal_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 3)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hctpre : c ++ FreeGroup.invRev t <+: palindrome c' t') : False := by
  -- the two weaker bands the self-piece and the meet collisions cost
  have hlam1 : lam ≤ 1 := by linarith
  have hlam2 : lam ≤ 1 / 2 := by linarith
  -- the two rotations are nonempty, which is all the absorb moves need
  have htne : t ≠ [] := ne_nil_of_mem_symmetrization hRne ht
  have ht'ne : t' ≠ [] := ne_nil_of_mem_symmetrization hRne ht'
  -- the two conjugators are reduced
  have hredc : FreeGroup.IsReduced c :=
    isReduced_of_infix ⟨[], t ++ FreeGroup.invRev c, by simp [palindrome]⟩ hredp
  have hredc' : FreeGroup.IsReduced c' :=
    isReduced_of_infix ⟨[], t' ++ FreeGroup.invRev c', by simp [palindrome]⟩ hredp'
  -- the two factors do not cancel
  have hcoin := mk_palindrome_mul_ne_one_of_minimal hmin
  have hP2 : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
    unfold palindrome
    rw [List.append_assoc]
  have hcpre : c <+: palindrome c' t' :=
    (show c <+: c ++ FreeGroup.invRev t from ⟨_, rfl⟩).trans hctpre
  have hc'pre : c' <+: palindrome c' t' := by
    rw [hP2]
    exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
  have hc't'pre : c' ++ t' <+: palindrome c' t' := ⟨FreeGroup.invRev c', rfl⟩
  have hctlen : (c ++ FreeGroup.invRev t).length = c.length + t.length := by
    rw [List.length_append, FreeGroup.invRev_length]
  have hc't'len : (c' ++ t').length = c'.length + t'.length := List.length_append
  rcases le_or_gt (c.length + t.length) c'.length with hA | hA
  · -- the whole inverted rotation sits inside the second conjugator
    obtain ⟨Z, hZ⟩ := List.prefix_of_prefix_length_le hctpre hc'pre (by omega)
    have hc'eq : c' = c ++ (FreeGroup.invRev t ++ Z) := by
      rw [← hZ, List.append_assoc]
    rw [hc'eq] at hmin hredc'
    exact not_absorb_inv_of_minimal hmin hredc' htne
  · rcases le_or_gt c'.length c.length with hB | hC
    · -- the second conjugator is the shorter one
      obtain ⟨q, hq⟩ := List.prefix_of_prefix_length_le hc'pre hcpre hB
      have hcq : c = c' ++ q := hq.symm
      have hclen : c.length = c'.length + q.length := by
        rw [hcq, List.length_append]
      rcases le_or_gt (c'.length + t'.length) c.length with hB1 | hB23
      · -- the whole second rotation sits inside the first conjugator
        obtain ⟨q'', hq''⟩ :=
          List.prefix_of_prefix_length_le hc't'pre hcpre (by omega)
        have hceq : c = c' ++ (t' ++ q'') := by
          rw [← hq'', List.append_assoc]
        rw [hceq] at hmin hredc
        exact not_absorb_of_minimal hmin hredc ht'ne
      · rcases le_or_gt (c'.length + t'.length) (c.length + t.length) with hB2 | hB3
        · -- the two rotations meet in a piece: the slide collision
          obtain ⟨W, hW⟩ :=
            List.prefix_of_prefix_length_le hc't'pre hctpre (by omega)
          have hcancel : t' ++ W = q ++ FreeGroup.invRev t := by
            have hb : c' ++ (t' ++ W) = c' ++ (q ++ FreeGroup.invRev t) := by
              rw [← List.append_assoc, hW, hcq, List.append_assoc]
            exact List.append_cancel_left hb
          have hq1 : q <+: q ++ FreeGroup.invRev t := ⟨_, rfl⟩
          have hq2 : t' <+: q ++ FreeGroup.invRev t := by
            rw [← hcancel]
            exact ⟨W, rfl⟩
          obtain ⟨p, hp⟩ := List.prefix_of_prefix_length_le hq1 hq2 (by omega)
          have hplen : q.length + p.length = t'.length := by
            have hb := congrArg List.length hp
            rw [List.length_append] at hb
            omega
          have hpW : p ++ W = FreeGroup.invRev t := by
            have hb : q ++ (p ++ W) = q ++ FreeGroup.invRev t := by
              rw [← List.append_assoc, hp, hcancel]
            exact List.append_cancel_left hb
          have hpt : p <+: FreeGroup.invRev t := ⟨W, hpW⟩
          have hqt' : q <+: t' := ⟨p, hp⟩
          by_cases hsame : FreeGroup.invRev t = t'.rotate q.length
          · exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt' hsame)
          · have hrot' : t'.rotate q.length = p ++ q := by
              rw [← hp, rotate_append]
            have hprot : p <+: t'.rotate q.length := by
              rw [hrot']
              exact ⟨q, rfl⟩
            have hpiece : IsPiece (symmetrization R) p :=
              isPiece_of_prefix_two (invRev_mem_symmetrization ht)
                (rotate_mem_symmetrization ht' q.length) hsame hpt hprot
            have hlt := hmetric p hpiece (t'.rotate q.length)
              (rotate_mem_symmetrization ht' q.length) hprot
            rw [List.length_rotate] at hlt
            have hplenq : (q.length : ℚ) + (p.length : ℚ) = (t'.length : ℚ) := by
              exact_mod_cast hplen
            have ht_eq : t = FreeGroup.invRev W ++ FreeGroup.invRev p := by
              have hb := congrArg FreeGroup.invRev hpW
              rw [FreeGroup.invRev_invRev, FreeGroup.invRev_append] at hb
              exact hb.symm
            rw [hcq, ht_eq, ← hp] at hmin
            rw [hcq] at hredc
            have hover := overhang_le_of_minimal hmin hredc
            have hp0 : (0 : ℚ) ≤ (p.length : ℚ) := Nat.cast_nonneg _
            have hslide : (p.length : ℚ)
                < lam * ((q.length : ℚ) + (p.length : ℚ)) := by
              rw [hplenq]
              exact hlt
            have hoverq : (q.length : ℚ) ≤ 2 * (p.length : ℚ) := by
              exact_mod_cast hover
            exact not_overhang_of_slide_sharp hlam0 hlam hp0 hslide hoverq
        · -- the second rotation covers the whole inverted first rotation
          have hstep : q ++ FreeGroup.invRev t <+: t' := by
            refine (List.prefix_append_right_inj c').mp ?_
            rw [← List.append_assoc, ← hcq]
            exact List.prefix_of_prefix_length_le hctpre hc't'pre (by omega)
          have hqt' : q <+: t' :=
            (show q <+: q ++ FreeGroup.invRev t from ⟨_, rfl⟩).trans hstep
          have hinvpre : FreeGroup.invRev t <+: t'.rotate q.length :=
            prefix_rotate_of_append_prefix hstep
          by_cases hsame : FreeGroup.invRev t = t'.rotate q.length
          · exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt' hsame)
          · have hpiece : IsPiece (symmetrization R) (FreeGroup.invRev t) :=
              isPiece_of_prefix_two (invRev_mem_symmetrization ht)
                (rotate_mem_symmetrization ht' q.length) hsame
                (List.prefix_refl _) hinvpre
            exact not_isPiece_self_sharp hlam1 hmetric
              (invRev_mem_symmetrization ht) hpiece
    · -- the second conjugator is the longer one
      obtain ⟨y, hy⟩ := List.prefix_of_prefix_length_le hcpre hc'pre (by omega)
      have hc'y : c' = c ++ y := hy.symm
      have hylen : c'.length = c.length + y.length := by
        rw [hc'y, List.length_append]
      have hP2' : palindrome c' t' = c ++ (y ++ (t' ++ FreeGroup.invRev c')) := by
        rw [hP2, hc'y, List.append_assoc]
      have hinvpre : FreeGroup.invRev t
          <+: y ++ (t' ++ FreeGroup.invRev c') := by
        refine (List.prefix_append_right_inj c).mp ?_
        rw [← hP2']
        exact hctpre
      have hyinv : y <+: FreeGroup.invRev t := by
        refine List.prefix_of_prefix_length_le
          (show y <+: y ++ (t' ++ FreeGroup.invRev c') from ⟨_, rfl⟩) hinvpre ?_
        rw [FreeGroup.invRev_length]
        omega
      obtain ⟨v, hv⟩ := hyinv
      have hvlen : y.length + v.length = t.length := by
        have hb := congrArg List.length hv
        rw [List.length_append, FreeGroup.invRev_length] at hb
        omega
      have hvpre : v <+: t' ++ FreeGroup.invRev c' := by
        refine (List.prefix_append_right_inj y).mp ?_
        rw [hv]
        exact hinvpre
      have hvrot : v <+: (FreeGroup.invRev t).rotate y.length := by
        rw [← hv, rotate_append]
        exact ⟨y, rfl⟩
      have hrotmem : (FreeGroup.invRev t).rotate y.length ∈ symmetrization R :=
        rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length
      by_cases hsame : t' = (FreeGroup.invRev t).rotate y.length
      · exact hcoin (mk_palindrome_mul_eq_one_of_coincidence' hc'y ⟨v, hv⟩ hsame)
      · rcases le_or_gt v.length t'.length with hC1 | hC2
        · -- the two rotations meet in a piece: the meet collision
          obtain ⟨u, hu⟩ := List.prefix_of_prefix_length_le hvpre
            (show t' <+: t' ++ FreeGroup.invRev c' from ⟨_, rfl⟩) hC1
          have hpiece : IsPiece (symmetrization R) v :=
            isPiece_of_prefix_two ht' hrotmem hsame ⟨u, hu⟩ hvrot
          have hlt := hmetric v hpiece ((FreeGroup.invRev t).rotate y.length)
            hrotmem hvrot
          rw [List.length_rotate, FreeGroup.invRev_length] at hlt
          have ht_eq : t = FreeGroup.invRev v ++ FreeGroup.invRev y := by
            have hb := congrArg FreeGroup.invRev hv
            rw [FreeGroup.invRev_invRev, FreeGroup.invRev_append] at hb
            exact hb.symm
          rw [hc'y, ht_eq, ← hu] at hmin
          rw [hc'y] at hredc'
          have hover := overhang_le_of_minimal_meet hmin hredc'
          have hv0 : (0 : ℚ) ≤ (v.length : ℚ) := Nat.cast_nonneg _
          have hsum : (y.length : ℚ) + (v.length : ℚ) = (t.length : ℚ) := by
            exact_mod_cast hvlen
          have hoverq : (y.length : ℚ) ≤ (v.length : ℚ) := by
            exact_mod_cast hover
          exact not_overhang_of_meet_sharp hlam0 hlam2 hv0 hsum hoverq hlt
        · -- the inverted first rotation covers the whole second rotation
          have ht'v : t' <+: v :=
            List.prefix_of_prefix_length_le
              (show t' <+: t' ++ FreeGroup.invRev c' from ⟨_, rfl⟩) hvpre
              (by omega)
          have ht'rot : t' <+: (FreeGroup.invRev t).rotate y.length :=
            ht'v.trans hvrot
          have hpiece : IsPiece (symmetrization R) t' :=
            isPiece_of_prefix_two ht' hrotmem hsame (List.prefix_refl _) ht'rot
          exact not_isPiece_self_sharp hlam1 hmetric ht' hpiece

/-- **The destroyed block never swallows the first rotation**, at any
`λ ≤ 1/3`, from the prefix rather than from confinement.  The sharp twin of
`GreendlingerRegime.swallow_bound_of_minimal_of_prefix`, with the same
signature and the constant moved.

The bound is read off the core by `False.elim`, which is what the `λ`-free proof
does too --- it obtains a swallowing shape it never consumes and then closes six
branches on the prefix alone. -/
theorem swallow_bound_of_minimal_of_prefix_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 3)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (_heq : palindrome c t = P' ++ M)
    (hctpre : c ++ FreeGroup.invRev t <+: palindrome c' t') :
    M.length ≤ c.length + t.length :=
  (not_adjacent_prefix_of_minimal_sharp hlam0 hlam hRne hmetric hmin ht ht'
    hredp hredp' hctpre).elim

/-- **The destroyed block never swallows the first rotation**, in the confined
shape the adjacent analysis produces.  The sharp twin of
`GreendlingerRegime.swallow_bound_of_minimal`, and the same three lines: a
swallowing block has `invRev M = c ++ invRev t ++ invRev c₂`, so confinement
exhibits `c ++ invRev t` as a prefix of the adjacent palindrome and the core
applies.

Here the contradiction hypothesis really is consumed --- it is what produces the
swallowing shape, and so the prefix. -/
theorem swallow_bound_of_minimal_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 3)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B') :
    M.length ≤ c.length + t.length := by
  by_contra hcon
  push Not at hcon
  obtain ⟨_c₁, c₂, _hc, _hc₂ne, _hM, hinvM⟩ := exists_swallow_split heq hcon
  have hpre : c ++ (FreeGroup.invRev t ++ FreeGroup.invRev c₂)
      <+: palindrome c' t' := by
    rw [← hinvM]
    exact ⟨B', heq'.symm⟩
  have hctpre : c ++ FreeGroup.invRev t <+: palindrome c' t' := by
    refine (show c ++ FreeGroup.invRev t
        <+: (c ++ FreeGroup.invRev t) ++ FreeGroup.invRev c₂ from
      ⟨_, rfl⟩).trans ?_
    rw [List.append_assoc]
    exact hpre
  exact not_adjacent_prefix_of_minimal_sharp hlam0 hlam hRne hmetric hmin ht ht'
    hredp hredp' hctpre

/-- **The block does not swallow the second rotation either**, at any
`λ ≤ 1/3`.  The sharp twin of `GreendlingerRegime.swallow_bound_of_minimal'`:
the same statement read backwards, since `conjInv` inverts the expression,
exchanges the two factors, inverts their rotations, and preserves minimality.

Neither the duality nor the bookkeeping sees `λ`; only the bound it transports
does. -/
theorem swallow_bound_of_minimal_sharp' [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 3)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M B' : List (α × Bool)} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R [(FreeGroup.mk c, t), (FreeGroup.mk c', t')] g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B') :
    M.length ≤ c'.length + t'.length := by
  have hinv := isMinimalConjExpr_conjInv hmin
  have hlist : conjInv [(FreeGroup.mk c, t), (FreeGroup.mk c', t')]
      = [(FreeGroup.mk c', FreeGroup.invRev t'),
        (FreeGroup.mk c, FreeGroup.invRev t)] := by
    simp [conjInv]
  rw [hlist] at hinv
  have hm1 : palindrome c' (FreeGroup.invRev t')
      = FreeGroup.invRev B' ++ M := by
    rw [← invRev_palindrome, heq', FreeGroup.invRev_append,
      FreeGroup.invRev_invRev]
  have hm2 : palindrome c (FreeGroup.invRev t)
      = FreeGroup.invRev M ++ FreeGroup.invRev P' := by
    rw [← invRev_palindrome, heq, FreeGroup.invRev_append]
  have hred1 : FreeGroup.IsReduced (palindrome c' (FreeGroup.invRev t')) := by
    rw [← invRev_palindrome]
    exact isReduced_invRev_iff.mpr hredp'
  have hred2 : FreeGroup.IsReduced (palindrome c (FreeGroup.invRev t)) := by
    rw [← invRev_palindrome]
    exact isReduced_invRev_iff.mpr hredp
  have hb := swallow_bound_of_minimal_sharp hlam0 hlam hRne hmetric hinv
    (invRev_mem_symmetrization ht') (invRev_mem_symmetrization ht) hred1 hred2
    hm1 hm2
  rwa [FreeGroup.invRev_length] at hb

/-! ## 2.  The block-search trichotomy at an arbitrary constant -/

/-- **A sharp Greendlinger subword beyond a position.**  The `λ`-twin of
`GreendlingerBeyond.SubwordBeyond`: the word `V` carries an arc longer than
`(1 - 3λ)` of a symmetrized relator, beginning at or after position `b`.

The structural layer is shared with the `λ`-free predicate, because
`GreendlingerSharpTwins` §4 already factors transport and inheritance through
`LocatedSplit`, which reads no bound. -/
def SubwordBeyondSharp (R : Set (List (α × Bool))) (lam : ℚ) (b : ℕ)
    (V : List (α × Bool)) : Prop :=
  ∃ n : ℕ, b ≤ n ∧ GreendlingerAtSharp R lam n V

/-- A located sharp subword is a sharp subword beyond its own position. -/
theorem subwordBeyondSharp_of_greendlingerAtSharp {R : Set (List (α × Bool))}
    {lam : ℚ} {b : ℕ} {V : List (α × Bool)} (h : GreendlingerAtSharp R lam b V) :
    SubwordBeyondSharp R lam b V :=
  ⟨b, le_rfl, h⟩

/-- A sharp subword beyond `b` is a sharp subword beyond anything smaller. -/
theorem SubwordBeyondSharp.of_le {R : Set (List (α × Bool))} {lam : ℚ}
    {b b' : ℕ} {V : List (α × Bool)} (h : SubwordBeyondSharp R lam b V)
    (hle : b' ≤ b) : SubwordBeyondSharp R lam b' V := by
  obtain ⟨n, hn, hat⟩ := h
  exact ⟨n, by omega, hat⟩

/-- The located conclusion, at exactly the block's length. -/
theorem greendlingerAtSharp_of_subwordBeyondSharp {R : Set (List (α × Bool))}
    {lam : ℚ} {b : ℕ} {V : List (α × Bool)}
    (h : SubwordBeyondSharp R lam b V) : GreendlingerAtSharp R lam b V := by
  obtain ⟨n, hn, hat⟩ := h
  exact hat.mono hn

/-- **Move one: the factor keeps enough.**  The `λ`-twin of
`GreendlingerBeyond.subwordBeyond_of_keeps`.

The block eats `b - |c'|` letters off the front of the rotation and the
factor's own block eats at most `k` off the back; if the two together stay
inside the budget `3λ|t'|`, the arc the sharp conclusion asks for sits at
position exactly `b`.

The `λ`-free hypothesis is `2(k + (b - |c'|)) < |t'|`, which is this budget at
`λ = 1/6`.  Nothing else moves: this is
`GreendlingerSharpTwins.greendlingerAtSharp_of_bounded_cancellation` with its
offset spent on the incoming block rather than on slack. -/
theorem subwordBeyondSharp_of_keeps {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6)
    {c' t' P'' M'' B'' : List (α × Bool)} {b k : ℕ}
    (ht' : t' ∈ symmetrization R)
    (hsplit : palindrome c' t' = P'' ++ M'')
    (hk : M''.length ≤ (FreeGroup.invRev c').length + k)
    (hb : c'.length ≤ b)
    (hkeep : (k : ℚ) + ((b - c'.length : ℕ) : ℚ)
      < 3 * lam * (t'.length : ℚ)) :
    SubwordBeyondSharp R lam b (P'' ++ B'') := by
  refine ⟨c'.length + (b - c'.length), by omega, ?_⟩
  exact greendlingerAtSharp_of_bounded_cancellation hlam ht' hsplit hk hkeep

/-- **Move two: carrying a sharp subword back across a cascade step.**  The
`λ`-twin of `GreendlingerBeyond.SubwordBeyond.compose`, and the same proof: the
move is `GreendlingerAtSharp.transport`, which touches neither the relator nor
the bound. -/
theorem SubwordBeyondSharp.compose {R : Set (List (α × Bool))} {lam : ℚ}
    {b b' N₀ : ℕ} {V V₂ A₀ : List (α × Bool)}
    (h : SubwordBeyondSharp R lam b' V₂)
    (hV : V = A₀ ++ V₂.drop N₀)
    (hstep : b + N₀ ≤ b' + A₀.length)
    (harrive : N₀ ≤ b') :
    SubwordBeyondSharp R lam b V := by
  obtain ⟨n, hn, hat⟩ := h
  refine ⟨A₀.length + (n - N₀), by omega, ?_⟩
  rw [hV]
  exact hat.transport A₀ (by omega)

/-- **The overrun case**, sharply.  When the block is at least as long as what
the factor in front of it keeps, the residual block is `b + N₀ - |A₀|`. -/
theorem subwordBeyondSharp_of_overrun {R : Set (List (α × Bool))} {lam : ℚ}
    {b N₀ : ℕ} {V V₂ A₀ : List (α × Bool)}
    (hV : V = A₀ ++ V₂.drop N₀)
    (hover : A₀.length ≤ b)
    (h : SubwordBeyondSharp R lam (b + N₀ - A₀.length) V₂) :
    SubwordBeyondSharp R lam b V :=
  h.compose hV (by omega) (by omega)

/-- **Everything after the factor the block stops in is beyond the block**,
sharply.  The block ends inside the survivor `A₀`, so every letter of what
follows lies beyond it and no arithmetic is needed. -/
theorem subwordBeyondSharp_of_stops_inside {R : Set (List (α × Bool))} {lam : ℚ}
    {b N₀ : ℕ} {V V₂ A₀ : List (α × Bool)}
    (hV : V = A₀ ++ V₂.drop N₀)
    (hstop : b ≤ A₀.length)
    (h : SubwordBeyondSharp R lam N₀ V₂) :
    SubwordBeyondSharp R lam b V :=
  h.compose hV (by omega) le_rfl

/-- **The regime split of the block search, at an arbitrary constant.**  The
`λ`-twin of `GreendlingerBeyond.blockStop_cases`.

Either the factor keeps its rotation inside the budget `3λ|t'|`, or the block
outruns everything the factor keeps, or the block stops strictly inside the
survivor with the budget already spent.  `k` is what the factor's own block eats
past its trailing conjugator, so `b - |c'|` and `k` are the two ends the
rotation is eaten from.

The `λ`-free split reads the same trichotomy against a half, because
`1 - 3λ = 1/2` there: the constant in `blockStop_cases` is the *conclusion*'s,
not the piece bound's, which is why the sharp split is against `3λ` and not
against `λ`.  The first two branches have the moves above; the third is the one
the classical curvature count is about, and it is no more closed here than it is
there. -/
theorem blockStop_cases_sharp {c' : List (α × Bool)} (lam : ℚ)
    (t' P'' : List (α × Bool)) (b k : ℕ) (_ : c'.length ≤ b) :
    (k : ℚ) + ((b - c'.length : ℕ) : ℚ) < 3 * lam * (t'.length : ℚ) ∨
      P''.length ≤ b ∨
      (b < P''.length ∧ 3 * lam * (t'.length : ℚ)
        ≤ (k : ℚ) + ((b - c'.length : ℕ) : ℚ)) := by
  rcases le_or_gt (3 * lam * (t'.length : ℚ))
    ((k : ℚ) + ((b - c'.length : ℕ) : ℚ)) with h | h
  · rcases le_or_gt P''.length b with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h2, h⟩)
  · exact Or.inl h

/-! ## 3.  The two-piece long-overhang branch at an arbitrary constant -/

/-- **Two disjoint sharp arcs.**  The `λ`-twin of
`GreendlingerInduction.TwoPieceConclusion`: the word splits so that two of its
blocks are each longer than `(1 - 3λ)` of a symmetrized relator.

The warning attached to the `λ`-free predicate carries over verbatim.  The
strengthening is *false* in the band between the two branches of the regime,
and stating it sharply does not make it true there --- what the twin buys is
that the branch which is provable stops forcing the constant. -/
def TwoPieceConclusionSharp (R : Set (List (α × Bool))) (lam : ℚ)
    (w : List (α × Bool)) : Prop :=
  ∃ A u₁ B u₂ C : List (α × Bool),
    w = A ++ u₁ ++ B ++ u₂ ++ C ∧
      (∃ r₁ ∈ symmetrization R, u₁ <+: r₁ ∧
        (1 - 3 * lam) * (r₁.length : ℚ) < (u₁.length : ℚ)) ∧
      (∃ r₂ ∈ symmetrization R, u₂ <+: r₂ ∧
        (1 - 3 * lam) * (r₂.length : ℚ) < (u₂.length : ℚ))

/-- Two disjoint sharp arcs are more than the sharp gate asks for. -/
theorem greendlingerSharp_of_twoPieceConclusionSharp
    {R : Set (List (α × Bool))} {lam : ℚ} {w : List (α × Bool)}
    (h : TwoPieceConclusionSharp R lam w) :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ (1 - 3 * lam) * (r.length : ℚ) < (u.length : ℚ) := by
  obtain ⟨A, u₁, B, u₂, C, hw, ⟨r₁, hr₁, hpre, hlt⟩, -⟩ := h
  refine ⟨r₁, hr₁, u₁, ?_, hpre, hlt⟩
  refine ⟨A, B ++ u₂ ++ C, ?_⟩
  rw [hw]
  simp only [List.append_assoc]

/-- **Two disjoint sharp arcs, both in `P'`.**  The `λ`-twin of
`GreendlingerTwoPieceRegime.twoPiece_of_long_overhang`.

When the first conjugator overhangs the second by `q` and `q` already exceeds
`(1 - 3λ)` of the second rotation, the two subwords are `q` and the surviving
prefix of the first rotation, consecutive inside `P'`.  Nothing of `B'` is used,
which is the content of the `λ`-free statement and is unchanged here: in this
branch the second factor contributes through the *conjugator* of the first
palindrome, not through what survives of its own rotation.

No band is needed.  The second arc costs one piece --- the eaten suffix, bounded
by `GreendlingerSharpTwins.length_lt_of_eaten` --- out of a budget of three, so
`one_piece_budget` and `survivor_gt_sharp` close it at every `λ` the metric
condition holds at.  The `λ`-free version needs `6|E| < |t|` where `2|E| < |t|`
would do, which is the same slack read at a sixth. -/
theorem twoPieceSharp_of_long_overhang {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c c' q t t' P' M B' E : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hc : c = c' ++ q) (hq : q <+: t')
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E))
    (hlong : (1 - 3 * lam) * (t'.length : ℚ) < (q.length : ℚ)) :
    TwoPieceConclusionSharp R lam (P' ++ B') := by
  have hEbound := length_lt_of_eaten hmetric ht hE hpiece
  have hEle : E.length ≤ t.length := hE.length_le
  obtain ⟨d, hP'⟩ := exists_split_take_of_bounded_cancellation heq hEle hlen
  refine ⟨c', q, [], t.take (t.length - E.length), d ++ B', ?_,
    ⟨t', ht', hq, hlong⟩, ⟨t, ht, List.take_prefix _ _, ?_⟩⟩
  · rw [hP', hc]
    simp only [List.append_assoc, List.nil_append]
  · have hlenu : (t.take (t.length - E.length)).length = t.length - E.length := by
      rw [List.length_take]
      omega
    rw [hlenu, Nat.cast_sub hEle]
    exact survivor_gt_sharp (one_piece_budget (Nat.cast_nonneg _) hEbound)

/-- The one-arc conclusion of the long-overhang branch, sharply, for callers
that only want it. -/
theorem greendlingerSharp_of_long_overhang {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c c' q t t' P' M B' E : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hc : c = c' ++ q) (hq : q <+: t')
    (hE : E <:+ t)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + E.length)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E))
    (hlong : (1 - 3 * lam) * (t'.length : ℚ) < (q.length : ℚ)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) :=
  greendlingerSharp_of_twoPieceConclusionSharp
    (twoPieceSharp_of_long_overhang hmetric ht ht' heq hc hq hE hlen hpiece hlong)

/-! ## 4.  The bridge every case ends at -/

/-- **A symmetrized relator occurring as a subword gives the sharp
conclusion.**  The `λ`-twin of `GreendlingerDescent.greendlinger_of_infix`.

At the half form the inequality `|s| < 2|u|` is just nonemptiness when `u` is
the whole relator, and `omega` reads it off.  Sharply it is
`(1 - 3λ)|t| < |t|`, which is `0 < 3λ|t|` --- so the twin asks for `0 < λ` as
well as for nonemptiness, and `GreendlingerSharpTwins.lam_pos_of_metric` supplies
that wherever the symmetrization has two distinct members.

That extra hypothesis is not an artifact.  At `λ ≤ 0` the sharp conclusion asks
for an arc longer than the relator it is a prefix of, so no word supplies it and
the free case genuinely fails; the half form hides this because it never
multiplies by `λ`. -/
theorem greendlingerSharp_of_infix {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : 0 < lam) {t w : List (α × Bool)}
    (ht : t ∈ symmetrization R) (htne : t ≠ []) (hinf : t <:+: w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  refine ⟨t, ht, t, hinf, List.prefix_refl _, ?_⟩
  have hpos : (0 : ℚ) < (t.length : ℚ) := by
    have hb : 0 < t.length := List.length_pos_iff.mpr htne
    exact_mod_cast hb
  linarith [mul_pos hlam hpos]

end SmallCancellationRouter
end GroupApproximation
