import GroupApproximation.Sofic.GreendlingerSharpLandingAux

/-!
# The two landing-side statements `GreendlingerThreeFactor` never twinned

`GreendlingerLandingProd` is already written at a general constant from its
first line: `StoppingAlternativeBetaSharp`, `DeepSegmentDichotomy`,
`LargeSegmentLands` and the whole spectator interface of its §10 carry `lam` as
a parameter, and `GreendlingerAlphaPlumb` and `GreendlingerBetaBranch` are
twinned declaration for declaration in `GreendlingerSharpTwins` §§7–8.  What is
*not* twinned is the file underneath them all: `GreendlingerThreeFactor` still
carries four theorems pinned at `MetricSmallCancellation R (1 / 6)`, and two of
them are on the live route.

This file supplies the two that are, and nothing else.

## §1.  Where the block cannot outrun the next factor

`GreendlingerLandingConfined` reduces the whole (β) side of the sharp gate to
one predicate, `NonConfinedBlockLands`: the block image `invRev M` does *not*
stay inside `palindrome c' t'`, and it must still land.  Every other
configuration is discharged there.

`GreendlingerThreeFactor.eaten_lt_of_long_next_conjugator` is the statement that
this configuration cannot arise in one of the two conjugator regimes.  When the
*next* conjugator is the longer one — `c ++ y = c'` — everything the block eats
past `c'` is matched against letters of the leading rotation, so it is a common
prefix of `t'` and of a rotation of `invRev t`, hence a piece; and a piece is
shorter than what the next factor keeps.  So the block stops inside, and
`confinement_of_tail_survival` turns that into confinement outright.

The `λ`-free file states the survivor hypothesis as `5|t'| < 12m` and reads the
piece bound as `6d < |t'|`, so that `omega` can compare a sixth against five
twelfths.  Stated rationally the comparison is direct: the piece bound is
`d < λ|t'|` and the survivor hypothesis is `λ|t'| ≤ m`, and the two meet with no
slack at all.  That is a genuine weakening of the hypothesis — `5|t'| < 12m`
asks the next factor to keep five twelfths where `λ|t'| ≤ m` asks it to keep a
`λ`-fraction — and the weakening is what makes the statement usable against
`LargeSegmentLands`, whose own hypothesis `λ|t| ≤ |E|` is denominated the same
way.

`not_nonConfined_of_long_next_conjugator_sharp` is the corollary in the exact
shape `NonConfinedBlockLands` presents: same `hM`, same tail equation, and the
conclusion is the negation of that predicate's last hypothesis.  So the open
leaf is asked only about the **hug** regime, where the leading conjugator is the
longer one and runs along the next rotation itself.  That is the regime
`GreendlingerThreeFactor`'s header identifies as the one no local re-expression
move decides, and `GreendlingerLandingProd`'s §10 prices at `(1/2 + λ)` against
a budget of `λ`.

Nothing here discharges `NonConfinedBlockLands`; it restricts where it has to be
asked, and the restriction costs a survivor witness the caller must supply.

## §2.  The obligation in its right form, at the sharp constant

`GreendlingerThreeFactor.TailSubwordBeyondBlock` is that file's own verdict on
what the descent needs: not `LeadingConfinement` — refuted by the configuration
in its header — but that the subword the rest of the product carries lies
*beyond* the block.  In the refuting configuration this holds while confinement
fails, because the third factor's rotation sits exactly where the block stops.

`TailSubwordBeyondBlockSharp` is its `λ`-twin, and the twinning is free: the
predicate's hypothesis list mentions no constant at all, so only the located
conclusion moves, from `GreendlingerAt` to `GreendlingerAtSharp`.  The gate
follows with no induction, exactly as in the `λ`-free file — either the block
stays inside the trailing conjugator and the whole leading rotation survives, or
the hypothesis hands over a subword beyond the block and
`greendlingerAtSharp_inherit` carries it into the word.

`tailSubwordBeyondBlock_of_sharp` records that the sharp obligation is at least
as strong as the `λ`-free one at every `λ ≤ 1/6`, through
`greendlingerAt_of_greendlingerAtSharp`, so the twin supersedes rather than
duplicates.

## Where the constants are spent

`0 < λ` twice: once for the zero offset in §2's two producer calls, through
`GreendlingerLandingProd.cast_zero_lt_lam_mul`, and once in §1's degenerate
branch, where the block does not reach the next conjugator at all and the bound
being asserted is `0 < λ|t'|`.  The `λ`-free file spends nothing at either,
because `6 · 0 < |t'|` is `0 < |t'|`.

`λ ≤ 1/6` only inside `greendlingerAtSharp_of_short_cancellation`, which is
where the half form's `2(k + j) < |t|` is met.  §1 does not read it: the piece
bound and the survivor bound are compared at `λ` directly.

Unconditional apart from `TailSubwordBeyondBlockSharp`, which is named at every
use.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The long-next-conjugator regime is confined, at any constant -/

/-- **The block cannot outrun the next rotation when the next conjugator is the
longer one, at an arbitrary constant.**  The `λ`-twin of
`GreendlingerThreeFactor.eaten_lt_of_long_next_conjugator`.

Past `c'` the block is matched against letters of the leading rotation, so what
it eats there is a common prefix of `t'` and of a rotation of `invRev t` — a
piece.  `C'(λ)` bounds it by `λ|t'|`, while the next factor keeps `m ≥ λ|t'|`;
so the block stops inside what the next factor keeps, and stops early enough
that a subword beginning a `λ`-fraction into the next rotation is untouched.

Both conclusions are what the descent's inheritance step consumes.  The `λ`-free
version reads the survivor hypothesis as `5|t'| < 12m` and the piece bound as
`6d < |t'|`, and lets `omega` compare a sixth against five twelfths; here the
two are compared at `λ` with nothing to spare, which is why the survivor
hypothesis weakens to `λ|t'| ≤ m`.

`0 < λ` and `0 < |t'|` are read only in the branch where the block does not
reach `c'` at all: there the conclusion degenerates to `0 < λ|t'|`, which the
`λ`-free file got for free from `6 · 0 < |t'|`. -/
theorem eaten_lt_of_long_next_conjugator_sharp {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam)
    (hmetric : MetricSmallCancellation R lam)
    {c t c' t' y E M W : List (α × Bool)} {m : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (ht'pos : 0 < t'.length)
    (hE : E <:+ t)
    (hinvM : FreeGroup.invRev M = c ++ FreeGroup.invRev E)
    (hMW : FreeGroup.invRev M <+: W)
    (hsurv : c' ++ t'.take m <+: W)
    (hm : m ≤ t'.length) (hmbig : lam * (t'.length : ℚ) ≤ (m : ℚ))
    (hcy : c ++ y = c')
    (hne : t' ≠ (FreeGroup.invRev t).rotate y.length) :
    ((M.length - c'.length : ℕ) : ℚ) < lam * (t'.length : ℚ) ∧
      M.length ≤ c'.length + m := by
  have hMl : (FreeGroup.invRev M).length = M.length := FreeGroup.invRev_length
  have ht'q : (0 : ℚ) < (t'.length : ℚ) := by exact_mod_cast ht'pos
  have hpos : (0 : ℚ) < lam * (t'.length : ℚ) := mul_pos hlam0 ht'q
  rcases le_or_gt M.length c'.length with hshort | hlong
  · have h0 : M.length - c'.length = 0 := by omega
    refine ⟨?_, by omega⟩
    rw [h0]
    exact_mod_cast hpos
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
    have hbnd := hmetric (t'.take d) hpiece t' ht' (List.take_prefix _ _)
    rw [hdlen] at hbnd
    have hdltq : (d : ℚ) < (m : ℚ) := lt_of_lt_of_le hbnd hmbig
    have hdlt : d < m := by exact_mod_cast hdltq
    have hdeq : M.length - c'.length = d := by omega
    refine ⟨lt_of_le_of_lt ?_ hbnd, by omega⟩
    exact_mod_cast hdeq.le

/-- **Confinement, in the long-next-conjugator regime.**  The block image stays
inside the next factor's palindrome as soon as that factor keeps a
`λ`-fraction of its rotation visible in the word the block is travelling
through.

This is `GreendlingerThreeFactor.confinement_of_tail_survival` fed the length
bound above, and it is the half of `LeadingConfinement` that is a theorem at
every constant.  The other half — the leading conjugator the longer, hugging the
next rotation — is the one no local move decides. -/
theorem confined_of_long_next_conjugator_sharp {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam)
    (hmetric : MetricSmallCancellation R lam)
    {c t c' t' y E M W : List (α × Bool)} {m : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (ht'pos : 0 < t'.length)
    (hE : E <:+ t)
    (hinvM : FreeGroup.invRev M = c ++ FreeGroup.invRev E)
    (hMW : FreeGroup.invRev M <+: W)
    (hsurv : c' ++ t'.take m <+: W)
    (hm : m ≤ t'.length) (hmbig : lam * (t'.length : ℚ) ≤ (m : ℚ))
    (hcy : c ++ y = c')
    (hne : t' ≠ (FreeGroup.invRev t).rotate y.length) :
    FreeGroup.invRev M <+: palindrome c' t' := by
  have hfit := (eaten_lt_of_long_next_conjugator_sharp hlam0 hmetric ht ht'
    ht'pos hE hinvM hMW hsurv hm hmbig hcy hne).2
  refine confinement_of_tail_survival hMW hsurv (List.take_prefix m t') ?_
  rw [List.length_take]
  omega

/-- **The open leaf is a hug-regime statement.**  In the shape
`GreendlingerLandingConfined.NonConfinedBlockLands` presents its instances — the
orientation `M = E ++ invRev c` and the tail equation for the expression headed
by the next factor — a next conjugator extending the leading one *forces*
confinement, so that predicate's final hypothesis
`¬(invRev M <+: palindrome c' t')` cannot be met there.

What the caller must supply is the survivor witness: `m` letters of `t'`
standing behind `c'` in the tail word, with `λ|t'| ≤ m`.  Every case of the
descent delivers such an `m` — the `λ`-free file records five twelfths — but the
predicate itself does not carry one, which is why this is a restriction of where
the leaf must be asked and not a discharge of it.

So the residual regime for `NonConfinedBlockLands` is the hug: `c'` a proper
prefix of `c`, the leading conjugator running along the next rotation, where the
intrusion is an overhang plus a piece and
`GreendlingerLandingProd.intrusion_lt_half_add_lam_of_hug_of_piece` prices the
shortfall. -/
theorem not_nonConfined_of_long_next_conjugator_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hmetric : MetricSmallCancellation R lam)
    {c t c' t' y E M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {m : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (ht'pos : 0 < t'.length)
    (hE : E <:+ t)
    (hM : M = E ++ FreeGroup.invRev c)
    (htail : (conjEval ((FreeGroup.mk c', t') :: f)).toWord
      = FreeGroup.invRev M ++ B')
    (hsurv : c' ++ t'.take m
      <+: (conjEval ((FreeGroup.mk c', t') :: f)).toWord)
    (hm : m ≤ t'.length) (hmbig : lam * (t'.length : ℚ) ≤ (m : ℚ))
    (hcy : c ++ y = c')
    (hne : t' ≠ (FreeGroup.invRev t).rotate y.length) :
    FreeGroup.invRev M <+: palindrome c' t' :=
  confined_of_long_next_conjugator_sharp hlam0 hmetric ht ht' ht'pos hE
    (invRev_eaten_block hM) ⟨B', htail.symm⟩ hsurv hm hmbig hcy hne

/-! ## 2.  The obligation in its right form, at the sharp constant -/

/-- **The `λ`-twin of `GreendlingerThreeFactor.TailSubwordBeyondBlock`.**  Not
that the leading block stops inside the next factor's palindrome — that is
`LeadingConfinement`, and the configuration in `GreendlingerThreeFactor`'s
header violates it — but that the subword the rest of the product carries lies
*beyond* the block, together with the bound that the block leaves the leading
rotation partly standing.

The hypothesis list is quoted verbatim from the `λ`-free predicate, because it
mentions no constant: the whole of the twinning is that the located conclusion
is read at `(1 - 3λ)` of its relator rather than at a half. -/
def TailSubwordBeyondBlockSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c' t' P' M : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g →
    palindrome c t = P' ++ M →
    FreeGroup.invRev M
      <+: (conjEval ((FreeGroup.mk c', t') :: e)).toWord →
    c.length < M.length →
    M.length ≤ c.length + t.length ∧
      GreendlingerAtSharp R lam M.length
        (conjEval ((FreeGroup.mk c', t') :: e)).toWord

/-- **The sharp gate, from the obligation in its right form.**  The `λ`-twin of
`GreendlingerThreeFactor.greendlinger_of_tailSubwordBeyondBlock`, and the same
proof: no induction is needed, because either the block stays inside the
trailing conjugator and the whole leading rotation survives, or the hypothesis
hands over a subword of the rest of the product lying beyond the block, which
`greendlingerAtSharp_inherit` carries into the word.

The offsets are all `0`, so `0 < λ` is what makes them admissible; the `λ`-free
file reads `6 · 0 < |t|` and spends nothing. -/
theorem greendlingerSharp_of_tailSubwordBeyondBlockSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hreg : TailSubwordBeyondBlockSharp R lam)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {e : List (FreeGroup α × List (α × Bool))}
    (hmin : IsMinimalConjExpr R e (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
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
          refine greendlingerSharp_of_greendlingerAtSharp (n := c.length + 0) ?_
          rw [hwe]
          exact greendlingerAtSharp_of_short_cancellation hlam ht heq (by omega)
            (cast_zero_lt_lam_mul hlam0 htpos)
      | cons y e'' =>
          obtain ⟨x₁, s₁⟩ := x
          obtain ⟨x₂, s₂⟩ := y
          obtain ⟨c, t, c', t', ht, ht', hredp, hredp', hmin₂⟩ :=
            exists_palindromic_isMinimalConjExpr hR hRne hmin
          have htpos : 0 < t.length :=
            List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin₂.2.1
          refine greendlingerSharp_of_greendlingerAtSharp (n := c.length + 0) ?_
          rw [hwe]
          have hcl : (FreeGroup.invRev c).length = c.length :=
            FreeGroup.invRev_length
          rcases le_or_gt M.length c.length with hshort | hlong
          · exact greendlingerAtSharp_of_short_cancellation hlam ht heq
              (by omega) (cast_zero_lt_lam_mul hlam0 htpos)
          · obtain ⟨hhigh, hsub⟩ :=
              hreg c t c' t' P' M e'' (FreeGroup.mk w) hmin₂ heq ⟨B', hgw.symm⟩
                hlong
            exact greendlingerAtSharp_inherit (n := M.length) heq hgw (by omega)
              le_rfl hsub

/-- The sharp Greendlinger conclusion along the same route: every nonempty
reduced word of the normal closure is normalized to a minimal expression and
handed to the theorem above. -/
theorem greendlingerConclusionSharp_of_tailSubwordBeyondBlockSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hreg : TailSubwordBeyondBlockSharp R lam) :
    GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  exact greendlingerSharp_of_tailSubwordBeyondBlockSharp hR hRne hlam0 hlam hreg
    hw hwne hmin

/-- **The sharp obligation subsumes the `λ`-free one.**  Both predicates have
the *same* hypothesis list — neither mentions a constant — so the implication is
`greendlingerAt_of_greendlingerAtSharp` applied to the located conclusion, and
it holds at every `λ ≤ 1/6`.

This is what makes the twin a replacement rather than a second obligation: a
proof of `TailSubwordBeyondBlockSharp` discharges
`GreendlingerThreeFactor.greendlinger_of_tailSubwordBeyondBlock`'s consumers
too. -/
theorem tailSubwordBeyondBlock_of_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (h : TailSubwordBeyondBlockSharp R lam) : TailSubwordBeyondBlock R := by
  intro c t c' t' P' M e g hmin heq hpre hlow
  obtain ⟨hhigh, hsub⟩ := h c t c' t' P' M e g hmin heq hpre hlow
  exact ⟨hhigh, greendlingerAt_of_greendlingerAtSharp hlam hsub⟩

/-- **`SharpGreendlingerGate` from a family of tail-subword obligations.**  The
same two-case assembly as
`GreendlingerSharpDropGate.sharpGreendlingerGate_of_cascadeLandingDropSharp`:
where some relator is nonempty the two side conditions the gate does not supply
— `0 < lam` and `∀ r ∈ R, r ≠ []` — are recovered from a piece of the empty
word, and where every relator is empty the normal closure is trivial and no
reduced nonempty word lies in it.

The argument is a hypothesis and nothing here discharges it; its `λ`-free
counterpart is open too. -/
theorem sharpGreendlingerGate_of_tailSubwordBeyondBlockSharp [DecidableEq α]
    (hreg : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → TailSubwordBeyondBlockSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α := by
  intro R lam hcyc hlam hmetric
  by_cases hex : ∃ r ∈ R, r ≠ []
  · obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := exists_two_distinct_symmetrization hcyc hex
    obtain ⟨r, hr, hrne⟩ := hex
    have hlam0 : 0 < lam :=
      lam_pos_of_metric hmetric hs₁ hs₂ hne (subset_symmetrization R hr) hrne
    have hRne : ∀ q ∈ R, q ≠ [] := fun q hq =>
      ne_nil_of_metric_lam hmetric hs₁ hs₂ hne (subset_symmetrization R hq)
    exact greendlingerConclusionSharp_of_tailSubwordBeyondBlockSharp hcyc hRne
      hlam0 hlam (hreg R lam hcyc hRne hlam0 hlam hmetric)
  · intro w hw hwne hmem
    exfalso
    push Not at hex
    have hsub : FreeGroup.mk '' R ⊆
        ((⊥ : Subgroup (FreeGroup α)) : Set (FreeGroup α)) := by
      rintro _ ⟨r, hr, rfl⟩
      have hone : FreeGroup.mk r = (1 : FreeGroup α) := by
        rw [hex r hr, ← FreeGroup.one_eq_mk]
      simp [hone]
    have hb := Subgroup.normalClosure_le_normal hsub hmem
    rw [Subgroup.mem_bot] at hb
    have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
      rw [hb]
      exact FreeGroup.one_eq_mk
    have h2 := FreeGroup.reduce.sound h1
    rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
    exact hwne h2

/-- The same on the router's own alphabet, which is the instance every
construction in this repository consumes. -/
theorem sharpGreendlingerGate_fin_two_of_tailSubwordBeyondBlockSharp
    (hreg : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → TailSubwordBeyondBlockSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_tailSubwordBeyondBlockSharp hreg

end SmallCancellationRouter
end GroupApproximation
