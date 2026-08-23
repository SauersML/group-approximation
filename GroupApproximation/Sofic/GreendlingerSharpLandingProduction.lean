import GroupApproximation.Sofic.GreendlingerSharpInvariant
import GroupApproximation.Sofic.GreendlingerLandingProd

/-!
# The composite landing, measured at the junction

`GreendlingerDeepInvariant.DeepCompositeLandsSharp` is the deep half of the
routing lane: in the deep regime the head's block has swallowed the adjacent
palindrome whole, and what is left is a *composite* block eating into the word
of the expression past that junction.  The predicate asks for a landing site for
that composite block, at depth `D + (N − |P'|)` inside `(conjEval f).toWord`.

This file measures that junction, and the measurement settles three things.

## 1.  Why `landsInSharp_of_forward_alignment` cannot be pointed at it

`GreendlingerDeepInvariant.landsInSharp_of_forward_alignment` is the only
producer of `LandsInSharp` that manufactures its own offset bound rather than
taking one.  Its numeric fields cap the block it can certify:
`le_of_forward_alignment_fields` reads the drop bound `N ≤ |c₃|`, the
containment `|A| + (|c₃| − N) + i ≤ |M|` and the fit
`b + N ≤ |A| + |c₃| + i` together and gets `b ≤ |M|`.  So the constructor can
never place a landing site deeper than the block `invRev M` it aligns against.

At the deep junction the block that prefixes `(conjEval f).toWord` and belongs
to the adjacent factor `(c₂, t₂)` is that factor's own leading cancellation
`M₂`, and `exists_junction_split` shows `|M₂| < D`: the composite block is
strictly longer, by exactly the depth `|M| − |P₂| > 0` by which the head's block
overran the adjacent survivor.  `lt_drop_of_forward_alignment_fields` puts the
two together: a forward alignment against `M₂` certifies `b < D`, and the deep
conclusion needs `b ≥ D`.  The gap is arithmetic, not geometric.

## 2.  What the obligation is equivalent to, one junction up

The same measurement runs the other way.  `LandsInSharp.compose` is stated in
`GreendlingerLandingProd` only in the direction that carries a landing site from
a tail word into the word in front of it.  But the junction is one common
remainder `B₂` split two ways — the word in front keeps `P₂`, the word behind
loses `invRev M₂` — so `(conjEval f).toWord` is itself
`invRev M₂ ++ (conjEval e).toWord.drop |P₂|`, and the same lemma carries a site
the other way.  `landsInSharp_across_junction` is that direction, and
`landsInSharp_deepComposite_of_head` composes it with the junction identity
`D + |P₂| = |M| + |M₂|`:

    a landing site of depth `|M| + (N − |P'|)` in `(conjEval e).toWord`
      ⟹ a landing site of depth `D + (N − |P'|)` in `(conjEval f).toWord`

with the factor budget unchanged.  The antecedent is a statement about the
head's *own* block `M`, which carries the head factor's provenance —
`invRev M = c ++ invRev E` with `E <:+ t` — and is therefore the block that
`GreendlingerSharpRigidity.intrusion_lt_of_forward_sharp` can speak to.  The
composite block never has to be described.

## 3.  Well-posedness, and the corner that refutes

`exists_junction_split` is `GreendlingerDeepInduction.exists_overrun_landing_drop`
with the arithmetic kept: the drop it produces satisfies
`D + |B'| = |(conjEval f).toWord|`, so it never runs past the end of the word.
That conjunct is not decoration.  `DeepCompositeLandsSharp` quantifies over an
arbitrary `D` subject only to `B' = (conjEval f).toWord.drop D`, and once
`B' = []` every large `D` satisfies that while the conclusion asks for a landing
site deeper than the word is long.  `ne_nil_of_deepCompositeLandsSharp` is the
resulting refutation criterion, the exact analogue of
`GreendlingerLandingProd.ne_nil_of_largeSegmentLands` on the shallow side.

Nothing here discharges `DeepCompositeLandsSharp`.

## Where the hypotheses go

`hRne` and `λ ≤ 1/6` are read only by the refutation criterion, through
`GreendlingerLandingProd.lt_length_of_landsInSharp_one`; `0 < λ` only by the
confined base case; `λ ≤ 1/2` only by `lam_mul_le_eaten_of_deep`.  The junction
measurement and the transfer read no constant at all.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The junction, measured -/

/-- **The head's block outruns the adjacent factor's survivor.**  In the
configuration the deep regime produces — the head's block `invRev M` prefixing
the tail word, and the adjacent factor keeping `P₂` of its own palindrome — the
block is strictly longer than that survivor.

The argument is the one `exists_overrun_landing_drop` makes in its `exfalso`
branch, isolated: both `invRev M` and `P₂` prefix the same word, so the shorter
prefixes the longer, and `P₂` prefixes `palindrome c₂ t₂`; if the block were the
shorter of the two it would be confined, which is what the deep regime
denies. -/
theorem junction_survivor_lt_block {c₂ t₂ P₂ M₂ B₂ M B' W : List (α × Bool)}
    (hpal : palindrome c₂ t₂ = P₂ ++ M₂)
    (hsplit : W = P₂ ++ B₂)
    (htail : W = FreeGroup.invRev M ++ B')
    (hconf : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂)) :
    P₂.length < M.length := by
  rcases le_or_gt M.length P₂.length with hle | hgt
  · exfalso
    have hMpre : FreeGroup.invRev M <+: W := ⟨B', htail.symm⟩
    have hPpre : P₂ <+: W := ⟨B₂, hsplit.symm⟩
    have hle' : (FreeGroup.invRev M).length ≤ P₂.length := by
      rw [FreeGroup.invRev_length]
      exact hle
    exact hconf
      ((List.prefix_of_prefix_length_le hMpre hPpre hle').trans ⟨M₂, hpal.symm⟩)
  · exact hgt

/-- **The junction split, with its arithmetic kept.**

`GreendlingerDeepInduction.exists_overrun_landing_drop` produces the number `D`
by which the head's block eats into the word past the junction, and then forgets
where that number came from.  This is the same construction with the three facts
it turns on recorded:

* `D + |B'| = |(conjEval f).toWord|` — the drop is well posed, so `B'` really is
  what survives rather than a truncation at the end of the word;
* `|M₂| < D` — the composite block is strictly longer than the adjacent
  factor's own leading cancellation, which is the overrun made numeric;
* `D + |P₂| = |M| + |M₂|` — the composite block is that factor's block plus the
  depth `|M| − |P₂|` by which the head's block ran past its survivor.

The third is the identity that lets a landing site cross the junction (§3); the
second is what rules the adjacent factor out as the head of a forward alignment
(§2). -/
theorem exists_junction_split [DecidableEq α]
    {c₂ t₂ M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))}
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (htail : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord
      = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂)) :
    ∃ (P₂ M₂ B₂ : List (α × Bool)) (D : ℕ),
      palindrome c₂ t₂ = P₂ ++ M₂ ∧
        (conjEval f).toWord = FreeGroup.invRev M₂ ++ B₂ ∧
        (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord = P₂ ++ B₂ ∧
        B' = (conjEval f).toWord.drop D ∧
        D + B'.length = (conjEval f).toWord.length ∧
        M₂.length < D ∧ D + P₂.length = M.length + M₂.length := by
  have heval : conjEval ((FreeGroup.mk c₂, t₂) :: f)
      = FreeGroup.mk ((conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord) :=
    (FreeGroup.mk_toWord).symm
  obtain ⟨P₂, M₂, B₂, heq₂, hgw₂, hwe₂⟩ :=
    exists_leading_cancellation FreeGroup.isReduced_toWord hredp₂ heval
  have hPM : P₂.length < M.length :=
    junction_survivor_lt_block heq₂ hwe₂ htail hover
  have hB₂ : B₂ = (conjEval f).toWord.drop M₂.length := by
    rw [hgw₂, drop_append_of_ge (FreeGroup.invRev M₂) M₂.length B₂
      (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
      Nat.sub_self, List.drop_zero]
  have hkey : B' = B₂.drop (M.length - P₂.length) := by
    have h1 : FreeGroup.invRev M ++ B' = P₂ ++ B₂ := by
      rw [← htail, hwe₂]
    have h2 : (FreeGroup.invRev M ++ B').drop M.length = B' := by
      rw [drop_append_of_ge (FreeGroup.invRev M) M.length B'
        (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
        Nat.sub_self, List.drop_zero]
    rw [← h2, h1, drop_append_of_ge P₂ M.length B₂ hPM.le]
  have hlenW : M.length + B'.length = P₂.length + B₂.length := by
    have hl := congrArg List.length (hwe₂.symm.trans htail)
    rw [List.length_append, List.length_append, FreeGroup.invRev_length] at hl
    omega
  have hlenT : (conjEval f).toWord.length = M₂.length + B₂.length := by
    rw [hgw₂, List.length_append, FreeGroup.invRev_length]
  have hlenB : B'.length = B₂.length - (M.length - P₂.length) := by
    rw [hkey, List.length_drop]
  refine ⟨P₂, M₂, B₂, M₂.length + (M.length - P₂.length), heq₂, hgw₂, hwe₂,
    ?_, by omega, by omega, by omega⟩
  rw [hkey, hB₂, drop_add M₂.length (M.length - P₂.length) (conjEval f).toWord]

/-! ## 2.  The cap the forward constructor carries -/

/-- **A forward alignment cannot certify a block longer than the one it aligns
against.**

The three numeric fields of
`GreendlingerDeepInvariant.landsInSharp_of_forward_alignment` bound the block
`b` by `|M|`.  Geometrically: the constructor places the landing factor's
conjugator and the intrusion into its rotation *inside* the block `invRev M`, so
the block it certifies stops inside `invRev M` too.

Recorded because it is what decides where that constructor can be pointed. -/
theorem le_of_forward_alignment_fields {c₃ M A : List (α × Bool)} {N i b : ℕ}
    (hN : N ≤ c₃.length)
    (hhigh : A.length + (c₃.length - N) + i ≤ M.length)
    (hfit : b + N ≤ A.length + c₃.length + i) :
    b ≤ M.length := by
  omega

/-- **The adjacent factor cannot host the composite block.**

Combining the cap with the junction measurement: a forward alignment whose block
is the adjacent factor's own leading cancellation `M₂` certifies only `b < D`,
while the deep conclusion asks for a landing site at depth `D + (N − |P'|)`,
which is at least `D`.

So no instantiation of
`GreendlingerDeepInvariant.landsInSharp_of_forward_alignment` with the adjacent
factor `(c₂, t₂)` as head reaches the depth `DeepCompositeLandsSharp` needs.
The head factor `(c, t)` is the only one whose block is long enough, and its
block prefixes `(conjEval e).toWord` rather than `(conjEval f).toWord` — which
is what §3 repairs. -/
theorem lt_drop_of_forward_alignment_fields [DecidableEq α]
    {c₂ t₂ M B' P₂ M₂ B₂ A c₃ : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {D N i b : ℕ}
    (hpal : palindrome c₂ t₂ = P₂ ++ M₂)
    (hsplit : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord = P₂ ++ B₂)
    (hgw : (conjEval f).toWord = FreeGroup.invRev M₂ ++ B₂)
    (htail : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord
      = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂))
    (hD : D + B'.length = (conjEval f).toWord.length)
    (hN : N ≤ c₃.length)
    (hhigh : A.length + (c₃.length - N) + i ≤ M₂.length)
    (hfit : b + N ≤ A.length + c₃.length + i) :
    b < D := by
  have hPM : P₂.length < M.length :=
    junction_survivor_lt_block hpal hsplit htail hover
  have hcap : b ≤ M₂.length := le_of_forward_alignment_fields hN hhigh hfit
  have hlenW : M.length + B'.length = P₂.length + B₂.length := by
    have hl := congrArg List.length (hsplit.symm.trans htail)
    rw [List.length_append, List.length_append, FreeGroup.invRev_length] at hl
    omega
  have hlenT : (conjEval f).toWord.length = M₂.length + B₂.length := by
    rw [hgw, List.length_append, FreeGroup.invRev_length]
  omega

/-! ## 3.  A landing site crosses the junction upwards -/

/-- **The other direction of `LandsInSharp.compose`.**  The junction is one
common remainder `B₂` split two ways: the word in front of it keeps `P₂`, and
the word behind it loses `invRev M₂`.
`GreendlingerLandingProd.LandsInSharp.compose` is written only for carrying a
site from the word behind into the word in front; since `Wf` is itself
`invRev M₂ ++ W.drop |P₂|`, the same lemma carries a site the other way, and the
block bookkeeping moves by `|P₂| − |M₂|`.

`hover` is the standing condition of every overrun step: the block has already
covered what the factor in front keeps. -/
theorem landsInSharp_across_junction [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {P₂ M₂ B₂ W Wf : List (α × Bool)} {b m : ℕ}
    (hsplit : W = P₂ ++ B₂)
    (htail : Wf = FreeGroup.invRev M₂ ++ B₂)
    (hover : M₂.length ≤ b)
    (h : LandsInSharp R lam (b + P₂.length - M₂.length) W m) :
    LandsInSharp R lam b Wf m := by
  have hV : Wf = FreeGroup.invRev M₂ ++ W.drop P₂.length := by
    rw [htail, hsplit, drop_append_of_ge P₂ P₂.length B₂ (le_refl P₂.length),
      Nat.sub_self, List.drop_zero]
  have hA : (FreeGroup.invRev M₂).length ≤ b := by
    rw [FreeGroup.invRev_length]
    exact hover
  have h' : LandsInSharp R lam (b + P₂.length - (FreeGroup.invRev M₂).length)
      W m := by
    rw [FreeGroup.invRev_length]
    exact h
  exact landsInSharp_of_overrun hV hA h'

/-- **The composite landing, from a landing for the head's own block.**

The junction measurement turns the block bookkeeping into the identity
`D + |P₂| = |M| + |M₂|`, and the crossing step then converts a landing site of
depth `|M| + k` in the word in front of the junction into one of depth `D + k`
in the word behind it, with the same factor budget.

`k` is a spectator: the descent reads it as `N − |P'|`, the letters the weakened
invariant drops beyond the head's survivor. -/
theorem landsInSharp_composite_of_head [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {c₂ t₂ M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {D k m : ℕ}
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (htail : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord
      = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂))
    (hD : D + B'.length = (conjEval f).toWord.length)
    (h : LandsInSharp R lam (M.length + k)
      (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord m) :
    LandsInSharp R lam (D + k) (conjEval f).toWord m := by
  obtain ⟨P₂, M₂, B₂, D₀, -, hgw₂, hwe₂, -, hD₀, hlt, hnum⟩ :=
    exists_junction_split hredp₂ htail hover
  have hbound : M₂.length ≤ D + k := by omega
  have hgoal : LandsInSharp R lam (D + k + P₂.length - M₂.length)
      (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord m := by
    rw [show D + k + P₂.length - M₂.length = M.length + k from by omega]
    exact h
  exact landsInSharp_across_junction hwe₂ hgw₂ hbound hgoal

/-- The tail of a deep configuration spells what the original tail spells.  The
normalization step of `GreendlingerDeepArc.exists_deep_tail_setup`, isolated so
that a hypothesis stated against `e` can be moved to the normalized tail. -/
theorem conjEval_tail_eq_of_minimal [DecidableEq α] {R : Set (List (α × Bool))}
    {c t c₂ t₂ : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g) :
    conjEval ((FreeGroup.mk c₂, t₂) :: f) = conjEval e := by
  have h1 := hmin₂.2.1
  have h2 := hmin.2.1
  rw [conjEval_cons] at h1 h2
  exact mul_left_cancel (h1.trans h2.symm)

/-- **The deep obligation, one junction up.**

Exactly the conclusion of `GreendlingerDeepInvariant.DeepCompositeLandsSharp`,
derived from a landing site for the head factor's *own* block inside the word
its cancellation acts on.  The composite block is never described.

This is what the deep leaf costs once the junction has been measured: a landing
site of depth `|M| + (N − |P'|)` in `(conjEval e).toWord`, among fewer than `|f|`
factors.  The block `M` there is a suffix of `palindrome c t`, so it carries the
head factor's provenance — the ingredient
`GreendlingerLandingProd.not_stoppingAlternativeBetaSharp` shows a per-factor
leaf cannot be stated without.

`hD` is supplied by `exists_junction_split`; `hover` by
`GreendlingerDeepVacuity.not_deep_confined`, which is how
`GreendlingerSharpInvariant.exists_postJunction_drop_sharp` reaches this
configuration in the first place. -/
theorem landsInSharp_deepComposite_of_head [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {N D : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂))
    (hD : D + B'.length = (conjEval f).toWord.length)
    (h : LandsInSharp R lam (M.length + (N - P'.length))
      (conjEval e).toWord f.length) :
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length := by
  have hev : conjEval ((FreeGroup.mk c₂, t₂) :: f) = conjEval e :=
    conjEval_tail_eq_of_minimal hmin hmin₂
  have htail' : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord
      = FreeGroup.invRev M ++ B' := by
    rw [hev]
    exact htail
  have h' : LandsInSharp R lam (M.length + (N - P'.length))
      (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord f.length := by
    rw [hev]
    exact h
  exact landsInSharp_composite_of_head hredp₂ htail' hover hD h'

/-! ## 4.  The base case, and the corner that refutes -/

/-- **The block that stops inside the next conjugator lands there.**  The
composite block's base case: `GreendlingerSharpTwins.landsInSharp_of_confined`
at offset `0`, with the zero offset made admissible by `0 < λ` and the
nonemptiness of the landing rotation.

Nothing about the deep regime enters; the lemma is named because it is the one
configuration of the composite block that needs no piece bound at all. -/
theorem landsInSharp_of_short_block [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam)
    {c' t' : List (α × Bool)} {f₀ : List (FreeGroup α × List (α × Bool))}
    {b m : ℕ}
    (ht' : t' ∈ symmetrization R)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f₀)
      (conjEval ((FreeGroup.mk c', t') :: f₀)))
    (hb : b ≤ c'.length) (hm : f₀.length < m) :
    LandsInSharp R lam b (conjEval ((FreeGroup.mk c', t') :: f₀)).toWord m :=
  landsInSharp_of_confined (i := 0) ht' hredp' hmin
    (cast_zero_lt_lam_mul hlam0
      (List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht')))
    (by omega) hm

/-- **The refutation criterion for the deep leaf.**  If
`DeepCompositeLandsSharp` holds then in every deep instance whose tail past the
junction is a single factor, the head's cancellation leaves something of that
factor's word standing.

Read the other way: exhibit a family satisfying the metric condition at some
`λ ≤ 1/6` and a deep configuration with `|f| = 1` whose composite block eats the
whole of `(conjEval f).toWord`, and the deep leaf is false for that family.  The
mechanism is `GreendlingerLandingProd.lt_length_of_landsInSharp_one`: a
one-factor landing expression spells exactly `palindrome c'' t''`, whose fields
leave the block strictly inside it.

This is the exact analogue of
`GreendlingerLandingProd.ne_nil_of_largeSegmentLands` on the shallow side, and
it is why `exists_junction_split` keeps `D + |B'| = |(conjEval f).toWord|`: the
predicate itself asks only `B' = (conjEval f).toWord.drop D`, which every large
`D` satisfies once `B'` is empty. -/
theorem ne_nil_of_deepCompositeLandsSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hdeep : DeepCompositeLandsSharp R lam)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    {N i D : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hN : N ≤ c.length + i)
    (hgt : c.length + t.length < M.length + i)
    (hf : f.length < e.length)
    (hD : B' = (conjEval f).toWord.drop D)
    (hlen : f.length = 1) : B' ≠ [] := by
  intro hnil
  have hland := hdeep c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp
    hredp₂ heq htail hlow hi hN hgt hf hD
  rw [hlen] at hland
  have hlt := lt_length_of_landsInSharp_one hRne hlam hland
  have hz : ((conjEval f).toWord.drop D).length = 0 := by
    rw [← hD, hnil, List.length_nil]
  rw [List.length_drop] at hz
  omega

/-! ## 5.  The deep regime is always a large-segment regime -/

/-- **The deep regime supplies `LargeSegmentLands`' own hypothesis.**

`GreendlingerLandingProd.LargeSegmentLands` owes an answer only where the head
has lost at least `λ` of its rotation.  Along the shallow side of the deep
boundary that threshold is never in question:
`GreendlingerSharpBackLoss.exists_deep_orientation_sharp` gives the strictly
stronger `(1 − λ)|t| < |E|`, and `λ ≤ 1 − λ` for every `λ ≤ 1/2`.

So the two residuals meet without a gap between them: an instance that is deep
already satisfies the large-segment hypothesis, and does not have to be handed
to the two-piece budget instead.

Stated at `λ ≤ 1/2` because that is all the comparison costs; every consumer
reads it at `λ ≤ 1/6`. -/
theorem lam_mul_le_eaten_of_deep {lam : ℚ} {c t M : List (α × Bool)} {i : ℕ}
    (hlam : lam ≤ 1 / 2)
    (hMsuf : M <:+ palindrome c t)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length)
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i) :
    ∃ E : List (α × Bool), M = E ++ FreeGroup.invRev c ∧
      FreeGroup.invRev M = c ++ FreeGroup.invRev E ∧
      E <:+ t ∧ lam * (t.length : ℚ) ≤ (E.length : ℚ) := by
  obtain ⟨E, hM, hinvM, hEt, hbig, -⟩ :=
    exists_deep_orientation_sharp hMsuf hlow hhigh hi hgt
  refine ⟨E, hM, hinvM, hEt, ?_⟩
  have hT : (0 : ℚ) ≤ (t.length : ℚ) := Nat.cast_nonneg t.length
  have hprod : (0 : ℚ) ≤ (1 / 2 - lam) * (t.length : ℚ) :=
    mul_nonneg (by linarith) hT
  linarith

end SmallCancellationRouter
end GroupApproximation
