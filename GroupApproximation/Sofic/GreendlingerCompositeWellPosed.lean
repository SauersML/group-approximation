import GroupApproximation.Sofic.GreendlingerSharpInduction
import GroupApproximation.Sofic.GreendlingerSharpLandingProduction

/-!
# The composite deep leaf, measured against its own drop

`GreendlingerDeepInvariant.DeepCompositeLandsSharp` quantifies over a number `D`
subject to one equation only, `B' = (conjEval f).toWord.drop D`, and then asks
for a landing site at depth `D + (N − |P'|)` inside `(conjEval f).toWord`.  That
equation pins `D` exactly when `B' ≠ []`; once `B'` is empty **every** `D` past
the end of the word satisfies it, and the conclusion then asks for a landing
site deeper than the word is long, which
`GreendlingerLandingProd.lt_length_of_landsInSharp_one` refutes outright at a
one-factor tail.  The refutation criterion
`ne_nil_of_deepCompositeLandsSharp` of
`GreendlingerSharpLandingProduction` records that; this file settles what the
criterion is worth.

## 1.  The drop is pinned, except at one point

`wellPosed_of_ne_nil` and `drop_lt_length_of_ne_nil`: as soon as `B' ≠ []` the
drop equation forces both `D + |B'| = |(conjEval f).toWord|` and
`D < |(conjEval f).toWord|`, and `eq_of_drop_eq_of_ne_nil` says two such drops
coincide.  So outside the corner the predicate's `D` is the *unique* number the
junction produces, and adding either fact as a hypothesis changes nothing.

Inside the corner nothing is pinned: `length_le_of_drop_eq_nil` is all the
equation says.

## 2.  How much of the corner the deep hypotheses already exclude

The predicate carries no small-cancellation hypothesis, but every consumer —
`GreendlingerDeepInvariant.greendlingerAtSharp_drop_of_lands` and
`greendlingerSharp_of_lands` — reads it beside `hRne`, `λ ≤ 1/6` and
`MetricSmallCancellation R lam`, so a proof of the leaf may use those.  Against
that background the leaf's own hypotheses already supply the junction condition:
`not_confined_of_deep` derives `¬ (invRev M <+: palindrome c₂ t₂)` from `hmin₂`
and the deep numerics, through
`GreendlingerSharpInduction.not_deep_confined_sharp`, exactly as
`GreendlingerDeepInvariant.exists_postJunction_drop` does.
`deep_junction_data` collects what follows:

* `f ≠ []` — the two-factor corner is empty, since a one-factor tail spells the
  adjacent palindrome and the block would be confined;
* `(conjEval f).toWord ≠ []` — the word the composite block travels is nonempty;
* a drop `D₀` that *is* well posed, `D₀ + |B'| = |(conjEval f).toWord|`, from
  `GreendlingerSharpLandingProduction.exists_junction_split`.

What none of this excludes is `B' = []` with `f ≠ []`: that is the statement
that the head's cancellation eats the tail word *whole*, and neither the
junction kill nor the drop arithmetic speaks to it.

## 3.  The arithmetic conjunct is not the repair

`exists_junction_split` keeps `D + |B'| = |(conjEval f).toWord|`, and it is
tempting to read that conjunct as the missing hypothesis.  It is not.  In the
corner the same conjunct is *satisfied*, at the single value
`D = |(conjEval f).toWord|` (`nil_eq_drop_length`,
`eq_length_of_wellPosed_of_nil`), and the conclusion is still a landing site at
depth `≥ |(conjEval f).toWord|`.
`not_deepCompositeLandsSharpWellPosed_of_collapse` refutes the arithmetic-repaired
predicate on exactly the instances that refute the original, so the arithmetic
narrows the corner from a ray to a point without closing it.

The minimal repair is `B' ≠ []`, which implies the arithmetic
(`deepCompositeLandsSharp'_of_wellPosed`) and is strictly stronger than it.
`DeepCompositeLandsSharp'` is the predicate with that hypothesis added, and
`deepCompositeLandsSharp_of_sharp'_of_noDeepCollapse` says the two agree once
`NoDeepCollapse` — the residual "no deep configuration eats its tail word
whole" — is discharged.  `NoDeepCollapse` is the honest name of what is missing;
`tail_ne_nil_of_deep` discharges its two-factor case and nothing here discharges
the rest.

## 4.  The repair costs the transfer nothing

`GreendlingerSharpLandingProduction.landsInSharp_deepComposite_of_head` takes the
arithmetic as an input.  `landsInSharp_deepComposite_of_head_of_ne_nil` and
`landsInSharp_deepComposite_of_head_of_deep` supply it from `B' ≠ []` and from
the leaf's own hypothesis set respectively, so the head-landing route into the
composite conclusion runs unchanged off the repaired predicate.

The same hole is present verbatim in the `λ`-free
`GreendlingerDeepInvariant.DeepCompositeLands`: same drop equation, same free
`D`, same `LandsIn … f.length` conclusion whose `f.length = 0` instance is
empty.  It is not a twinning artifact.

Nothing here discharges `DeepCompositeLandsSharp`, `DeepCompositeLandsSharp'`
or `NoDeepCollapse`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  A drop is pinned by its remainder, except at one point -/

/-- **A nonempty remainder pins the drop.**  If `B` is what survives dropping
`D` letters and something survives, then `D` counts letters that are really
there.  This is the arithmetic
`GreendlingerSharpLandingProduction.exists_junction_split` keeps, available from
the drop equation alone as soon as the remainder is nonempty. -/
theorem wellPosed_of_ne_nil {V B : List (α × Bool)} {D : ℕ}
    (hD : B = V.drop D) (hne : B ≠ []) : D + B.length = V.length := by
  have hlen : B.length = V.length - D := by
    rw [hD, List.length_drop]
  have hpos : 0 < B.length := List.length_pos_iff.mpr hne
  omega

/-- **A nonempty remainder puts the drop strictly inside the word.**  This is
the inequality the composite conclusion needs and the corner denies. -/
theorem drop_lt_length_of_ne_nil {V B : List (α × Bool)} {D : ℕ}
    (hD : B = V.drop D) (hne : B ≠ []) : D < V.length := by
  have hlen := wellPosed_of_ne_nil hD hne
  have hpos : 0 < B.length := List.length_pos_iff.mpr hne
  omega

/-- **Outside the corner the drop is unique.**  Two numbers leaving the same
nonempty remainder are the same number, so `DeepCompositeLandsSharp`'s free `D`
is not free at all wherever `B' ≠ []`: it is the drop the junction produces. -/
theorem eq_of_drop_eq_of_ne_nil {V B : List (α × Bool)} {D D' : ℕ}
    (hD : B = V.drop D) (hD' : B = V.drop D') (hne : B ≠ []) : D = D' := by
  have h := wellPosed_of_ne_nil hD hne
  have h' := wellPosed_of_ne_nil hD' hne
  omega

/-- **In the corner the equation says only this.**  An empty remainder bounds
the drop from below and leaves it otherwise unconstrained — the whole of the
defect. -/
theorem length_le_of_drop_eq_nil {V B : List (α × Bool)} {D : ℕ}
    (hD : B = V.drop D) (hnil : B = []) : V.length ≤ D := by
  have hlen : B.length = V.length - D := by
    rw [hD, List.length_drop]
  rw [hnil, List.length_nil] at hlen
  omega

/-- The corner is inhabited by the drop equation: dropping the whole word leaves
nothing. -/
theorem nil_eq_drop_length (V : List (α × Bool)) :
    ([] : List (α × Bool)) = V.drop V.length := by
  have h : (V.drop V.length).length = 0 := by
    rw [List.length_drop, Nat.sub_self]
  exact (List.length_eq_zero_iff.mp h).symm

/-- **The arithmetic conjunct, in the corner.**  Requiring
`D + |B'| = |(conjEval f).toWord|` does not empty the corner; it selects one
point of it, the drop that removes the whole word. -/
theorem eq_length_of_wellPosed_of_nil {V B : List (α × Bool)} {D : ℕ}
    (hlen : D + B.length = V.length) (hnil : B = []) : D = V.length := by
  rw [hnil, List.length_nil] at hlen
  omega

/-! ## 2.  What the deep leaf's own hypotheses already supply -/

/-- **The junction condition is not an extra assumption.**  The overrun
hypothesis `¬ (invRev M <+: palindrome c₂ t₂)` that every junction lemma of the
deep lane takes is derivable from `DeepCompositeLandsSharp`'s own hypothesis
set, against the background every consumer already carries.

This is `GreendlingerDeepInvariant.exists_postJunction_drop`'s `by_cases` step,
made available to a *prover* of the leaf rather than to its producer: the
adjacent factor `(c₂, t₂)` is named in `hmin₂`, so the confined branch is
already contradictory where the leaf is stated. -/
theorem not_confined_of_deep [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c₂ t₂ P' M : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {i : ℕ}
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (hlow : c.length < M.length)
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i) :
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) := by
  rintro ⟨B₀, hB₀⟩
  exact not_deep_confined_sharp hlam hRne hmetric hmin₂ ht ht₂ hredp hredp₂ heq
    hB₀.symm hlow hi hgt

/-- **A one-factor tail cannot host an overrun.**  If the expression past the
junction is empty, the tail word *is* the adjacent palindrome, so the block is
confined.  The nil branch of
`GreendlingerDeepInduction.deepOverrunArc_of_landing`, isolated. -/
theorem tail_ne_nil_of_not_confined [DecidableEq α]
    {c₂ t₂ M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))}
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (htail : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord
      = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂)) : f ≠ [] := by
  rintro rfl
  exact hover ⟨B', htail.symm.trans (toWord_conjEval_singleton hredp₂)⟩

/-- **The junction, measured from the leaf's own hypotheses.**

Everything the deep leaf can extract about its own configuration without any
further input: the junction condition, the nonemptiness of the post-junction
expression and of the word it spells, and a drop that is well posed.

The last conjunct is the point of the lemma.  A well-posed drop always exists;
what the predicate's hypothesis `B' = (conjEval f).toWord.drop D` does *not* say
is that the `D` it is handed is that one.  By `eq_of_drop_eq_of_ne_nil` the two
agree wherever `B' ≠ []`, and diverge only there. -/
theorem deep_junction_data [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {i : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length)
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i) :
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) ∧ f ≠ [] ∧
      (conjEval f).toWord ≠ [] ∧
      ∃ D₀ : ℕ, B' = (conjEval f).toWord.drop D₀ ∧
        D₀ + B'.length = (conjEval f).toWord.length := by
  have hover := not_confined_of_deep hlam hRne hmetric hmin₂ ht ht₂ hredp
    hredp₂ heq hlow hi hgt
  have hev : conjEval ((FreeGroup.mk c₂, t₂) :: f) = conjEval e :=
    conjEval_tail_eq_of_minimal hmin hmin₂
  have htail' : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord
      = FreeGroup.invRev M ++ B' := by
    rw [hev]
    exact htail
  obtain ⟨_P₂, M₂, _B₂, D₀, _, _, _, hdrop, hlenD, hlt, _⟩ :=
    exists_junction_split hredp₂ htail' hover
  have hWne : (conjEval f).toWord ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at hlenD
    omega
  exact ⟨hover, tail_ne_nil_of_not_confined hredp₂ htail' hover, hWne, D₀,
    hdrop, hlenD⟩

/-- **The two-factor corner is empty.**  The `f = []` half of the collapse — the
one where the conclusion `LandsInSharp R lam _ _ 0` is unsatisfiable outright,
since it asks for a landing expression shorter than the empty one — does not
occur in the deep regime. -/
theorem tail_ne_nil_of_deep [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {i : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length)
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i) : f ≠ [] :=
  (deep_junction_data hlam hRne hmetric hmin hmin₂ ht ht₂ hredp hredp₂ heq
    htail hlow hi hgt).2.1

/-! ## 3.  The two candidate repairs, and which one closes the corner -/

/-- **The leaf with the drop arithmetic added.**  `DeepCompositeLandsSharp` with
the conjunct `GreendlingerSharpLandingProduction.exists_junction_split` keeps,
`D + |B'| = |(conjEval f).toWord|`, moved into the hypothesis list.

Every other field is quoted verbatim from
`GreendlingerDeepInvariant.DeepCompositeLandsSharp`. -/
def DeepCompositeLandsSharpWellPosed [DecidableEq α]
    (R : Set (List (α × Bool))) (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ : List (α × Bool))
    (e f : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (N i D : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (i : ℚ) < lam * (t.length : ℚ) →
    N ≤ c.length + i →
    c.length + t.length < M.length + i →
    f.length < e.length →
    B' = (conjEval f).toWord.drop D →
    D + B'.length = (conjEval f).toWord.length →
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length

/-- **The leaf with the collapse excluded — the minimal repair.**
`DeepCompositeLandsSharp` with `B' ≠ []` in the hypothesis list and nothing
else changed.

`B' ≠ []` implies the arithmetic conjunct (`wellPosed_of_ne_nil`) and is
strictly stronger than it, since the arithmetic still admits the single
collapsed point `D = |(conjEval f).toWord|`.  It is also the exact condition
under which the predicate's `D` is the drop the junction produces
(`eq_of_drop_eq_of_ne_nil`), so on the repaired predicate `D` carries the
provenance the composite block's depth is supposed to have. -/
def DeepCompositeLandsSharp' [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ : List (α × Bool))
    (e f : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (N i D : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (i : ℚ) < lam * (t.length : ℚ) →
    N ≤ c.length + i →
    c.length + t.length < M.length + i →
    f.length < e.length →
    B' = (conjEval f).toWord.drop D →
    B' ≠ [] →
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length

/-- **The residual the repair leaves behind.**  No deep configuration has its
tail word eaten whole.

This is the difference between the repaired leaf and the original, and it is a
statement about *configurations*, not about landing sites: it says the head's
cancellation, however deep, always leaves a letter of the post-junction word
standing.  `tail_ne_nil_of_deep` settles its two-factor case — an empty `f`
would make the block confined — and nothing here settles the rest. -/
def NoDeepCollapse [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ : List (α × Bool))
    (e f : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (i : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (i : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + i →
    B' ≠ []

/-- The original leaf implies the arithmetic-repaired one: the extra hypothesis
is simply discarded. -/
theorem deepCompositeLandsSharpWellPosed_of_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (h : DeepCompositeLandsSharp R lam) :
    DeepCompositeLandsSharpWellPosed R lam := by
  intro c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq htail
    hlow hi hN hgt hf hD _
  exact h c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq
    htail hlow hi hN hgt hf hD

/-- The arithmetic-repaired leaf implies the collapse-repaired one: `B' ≠ []`
supplies the arithmetic.  With `deepCompositeLandsSharpWellPosed_of_sharp` this
orders the three predicates,
`DeepCompositeLandsSharp → DeepCompositeLandsSharpWellPosed →
DeepCompositeLandsSharp'`, and
`not_deepCompositeLandsSharpWellPosed_of_collapse` shows the first arrow is not
where the defect is repaired. -/
theorem deepCompositeLandsSharp'_of_wellPosed [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (h : DeepCompositeLandsSharpWellPosed R lam) :
    DeepCompositeLandsSharp' R lam := by
  intro c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq htail
    hlow hi hN hgt hf hD hne
  exact h c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq
    htail hlow hi hN hgt hf hD (wellPosed_of_ne_nil hD hne)

/-- The original leaf implies the collapse-repaired one. -/
theorem deepCompositeLandsSharp'_of_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (h : DeepCompositeLandsSharp R lam) : DeepCompositeLandsSharp' R lam :=
  deepCompositeLandsSharp'_of_wellPosed
    (deepCompositeLandsSharpWellPosed_of_sharp h)

/-- **The repair is exact.**  With the collapse residual discharged, the
repaired leaf gives back the original: the two predicates differ only over the
configurations `NoDeepCollapse` denies. -/
theorem deepCompositeLandsSharp_of_sharp'_of_noDeepCollapse [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (h : DeepCompositeLandsSharp' R lam) (hno : NoDeepCollapse R lam) :
    DeepCompositeLandsSharp R lam := by
  intro c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq htail
    hlow hi hN hgt hf hD
  exact h c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq
    htail hlow hi hN hgt hf hD
    (hno c t c₂ t₂ e f g P' M B' i hmin hmin₂ ht ht₂ hredp hredp₂ heq htail
      hlow hi hgt)

/-- **The arithmetic conjunct does not close the corner.**

A deep configuration whose head cancellation eats the post-junction word whole,
with a one-factor tail, refutes the *arithmetic-repaired* predicate — not only
the original.  The witnessing drop is `D = |(conjEval f).toWord|`, which
satisfies `B' = (conjEval f).toWord.drop D` and the arithmetic conjunct
simultaneously, and the conclusion then places a landing site at
depth at least the length of the word it travels, which
`GreendlingerLandingProd.not_landsInSharp_one_of_length_le` forbids.

So `GreendlingerSharpLandingProduction.ne_nil_of_deepCompositeLandsSharp`
survives the arithmetic repair verbatim: the criterion is a criterion about
`B'`, and only `B' ≠ []` answers it. -/
theorem not_deepCompositeLandsSharpWellPosed_of_collapse [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {N i : ℕ}
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
    (hf : f.length < e.length) (hlen : f.length = 1) (hnil : B' = []) :
    ¬ DeepCompositeLandsSharpWellPosed R lam := by
  subst hnil
  intro hdeep
  have hland := hdeep c t c₂ t₂ e f g P' M [] N i (conjEval f).toWord.length
    hmin hmin₂ ht ht₂ hredp hredp₂ heq htail hlow hi hN hgt hf
    (nil_eq_drop_length (conjEval f).toWord) (by simp)
  rw [hlen] at hland
  exact not_landsInSharp_one_of_length_le hRne hlam
    (Nat.le_add_right (conjEval f).toWord.length (N - P'.length)) hland

/-- The same instance refutes the original predicate, through the ordering. -/
theorem not_deepCompositeLandsSharp_of_collapse [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {N i : ℕ}
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
    (hf : f.length < e.length) (hlen : f.length = 1) (hnil : B' = []) :
    ¬ DeepCompositeLandsSharp R lam := fun h =>
  not_deepCompositeLandsSharpWellPosed_of_collapse hRne hlam hmin hmin₂ ht ht₂
    hredp hredp₂ heq htail hlow hi hN hgt hf hlen hnil
    (deepCompositeLandsSharpWellPosed_of_sharp h)

/-- **The collapse residual is exactly what the criterion asks for.**  If no
deep configuration collapses then in particular none collapses at a one-factor
tail, which is the shape
`GreendlingerSharpLandingProduction.ne_nil_of_deepCompositeLandsSharp` tests.
Stated so the sweep can be pointed at `NoDeepCollapse` rather than at the leaf:
a counterexample to the former is a counterexample to the latter, and is found
without ever exhibiting a landing site. -/
theorem ne_nil_of_noDeepCollapse [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hno : NoDeepCollapse R lam)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {i : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i) : B' ≠ [] :=
  hno c t c₂ t₂ e f g P' M B' i hmin hmin₂ ht ht₂ hredp hredp₂ heq htail hlow
    hi hgt

/-! ## 4.  The transfer, off the repaired hypothesis set -/

/-- **The head-landing transfer, from `B' ≠ []`.**
`GreendlingerSharpLandingProduction.landsInSharp_deepComposite_of_head` takes
the drop arithmetic as an input; on the repaired predicate that input is free,
so the route from a landing site for the head factor's *own* block to the
composite conclusion is unchanged by the repair. -/
theorem landsInSharp_deepComposite_of_head_of_ne_nil [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {N D : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂))
    (hD : B' = (conjEval f).toWord.drop D) (hne : B' ≠ [])
    (h : LandsInSharp R lam (M.length + (N - P'.length))
      (conjEval e).toWord f.length) :
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length :=
  landsInSharp_deepComposite_of_head hmin hmin₂ hredp₂ htail hover
    (wellPosed_of_ne_nil hD hne) h

/-- **The head-landing transfer, off the leaf's own hypothesis set.**  The same
step with the junction condition derived rather than assumed, so the only input
beyond `DeepCompositeLandsSharp'`'s hypotheses is a landing site for the head's
own block.

This is what the repaired deep leaf costs: a landing site of depth
`|M| + (N − |P'|)` in `(conjEval e).toWord` among fewer than `|f|` factors.  The
block `M` there is a suffix of `palindrome c t`, so it carries the head factor's
provenance — which is the ingredient
`GreendlingerLandingProd.not_stoppingAlternativeBetaSharp` shows a per-factor
leaf cannot be stated without. -/
theorem landsInSharp_deepComposite_of_head_of_deep [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {N i D : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i)
    (hD : B' = (conjEval f).toWord.drop D) (hne : B' ≠ [])
    (h : LandsInSharp R lam (M.length + (N - P'.length))
      (conjEval e).toWord f.length) :
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length :=
  landsInSharp_deepComposite_of_head_of_ne_nil hmin hmin₂ hredp₂ htail
    (not_confined_of_deep hlam hRne hmetric hmin₂ ht ht₂ hredp hredp₂ heq hlow
      hi hgt)
    hD hne h

end SmallCancellationRouter
end GroupApproximation
