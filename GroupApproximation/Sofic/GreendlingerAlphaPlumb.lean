import GroupApproximation.Sofic.GreendlingerBetaBranch

/-!
# Case (α), plumbed: the residual is the (β) regime and nothing else

`GreendlingerCascade` reduces the free-group half-form gate to `CascadeLanding`,
and `GreendlingerBetaBranch.cascadeLanding_of_deepArc_of_landing` splits that
into `DeepArcSource` and `LandingProduction` by casing on whether the block plus
the surviving stretch still fits inside the head palindrome.

Case (α) --- the conjugator-absorbed branch, `i_c = 0` --- is closed at instance
level: `GreendlingerDeepestMatch.landsIn_of_conjugatorAbsorbed` produces the
landing site from the double piece bound, and
`GreendlingerCoincidence.invRev_ne_rotate_of_minimal` supplies the distinctness
it needs from minimality alone, through the effective conjugator
`mk d = conjEval e₁ * mk c'`.  What neither file does is *plumb* that instance
into the descent: both take the positional pile --- which factor the block lands
in, the intrusion, the cascade's `A` and `N`, the minimality and the
symmetrization of the landing factor --- as a list of hypotheses, and nothing
says which of them the descent already has.

This file says it.

## What the descent already has

`ConjugatorAbsorbedSite` below names the (α) data, and it names only the part
that is genuinely open.  Everything else in the pile is derived here from
`CascadeLanding`'s own hypothesis context:

* `t' ∈ symmetrization R` --- from `ConjValid`, since the landing factor is a
  factor of the expression;
* `IsMinimalConjExpr R ((mk c', t') :: f) (conjEval ((mk c', t') :: f))` --- from
  `GreendlingerThreeFactor.isMinimalConjExpr_drop`, the landing factor's own
  suffix being a suffix of a minimal expression;
* `f.length < e.length` --- from the decomposition of `e`, which is what makes
  the descent terminate;
* the distinctness `invRev t ≠ t'.rotate |q|` --- from minimality, via the
  effective conjugator;
* `E`, the relator segment, together with `M = E ++ invRev c` and `E <:+ t` ---
  from `GreendlingerDeepestMatch.eaten_prefix_orientation`, which is available
  the moment the block outruns the trailing conjugator;
* the cascade decomposition `W = A ++ W'.drop N` itself --- from
  `GreendlingerCascade.exists_cascade`, recorded as `exists_cascade_split`.

So the site is: *where* the block lands (the split of `e`, with that factor in
palindromic normal form), the overhang `c = d ++ q` of the head conjugator past
the landing factor's effective conjugator with `q` a prefix of its rotation, the
intrusion `invRev E <+: t'.rotate |q|`, and the two inequalities that place the
end of the block inside `|c'| + |E|` of the landing word.  Nothing else.

The two inequalities are where `i_c = 0` is actually spent, and they are not
decoration.  Read them at the adjacent instance, `e₁ = []` with `A = []` and
`N = 0`: the block eats `|c| + |E| = |c'| + |q| + |E|` letters of a word that is
the landing word itself, and the fit demands it stop by `|c'| + |E|`, so `q` is
forced empty.  A nonempty overhang at an adjacent factor is exactly the case
where conjugator letters reach into relator territory, which is the (β) regime;
the site cannot name it, and does not try to.

## What is left

`LandingProductionBeta` is `LandingProduction` with the whole orientation
package handed to it and with the extra hypothesis that no conjugator-absorbed
site exists.  `landingProduction_of_beta` cases on that existence classically:
the positive branch is discharged here, the negative branch is the residual.
So the (α) regime is retired from the burden rather than merely proved
somewhere, and `cascadeLanding_of_deepArc_of_beta` states the gate over exactly
`DeepArcSource` and `LandingProductionBeta` --- both (β)-side --- plus
`C'(1/6)`.

One caveat, stated because the negation makes it harmless.  A site can be named
only when the landing factor appears in `e` already in palindromic normal form;
`GreendlingerThreeFactor.exists_palindromic_head` and `exists_palindromic_snd`
normalize the first two factors of an expression and there is no lemma for a
general position.  An instance whose landing factor is unnormalized therefore
falls to the residual predicate, which is sound --- that predicate assumes only
that no site exists --- and which is the reason the split is drawn against the
existence of the data rather than against an arithmetic condition on `i_c`.

Unconditional apart from `C'(1/6)`, which enters exactly where
`landsIn_of_conjugatorAbsorbed` reads the piece bound.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The (α) site -/

/-- **The conjugator-absorbed landing site.**  The block that the head factor
loses stops in the factor `(mk c', t')` of `e`, and it stops there in the
conjugator-absorbed way: the head conjugator `c` overhangs that factor's
*effective* conjugator --- the one it presents in the tail word, `mk d =
conjEval e₁ * mk c'` --- by a prefix `q` of its rotation, the deep eaten letters
`invRev E` continue along that rotation from `q`, and the cascade places the end
of the block within `|c'| + |E|` of the start of the landing factor's own word.

Nothing here mentions `R`: the site is word geometry, and every relator-side
fact the landing needs is derived from minimality at the point of use.  `E` is
the relator segment of `GreendlingerDeepestMatch.eaten_prefix_orientation` and
`M` enters only through its length. -/
def ConjugatorAbsorbedSite [DecidableEq α] (c E M : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) : Prop :=
  ∃ (e₁ f : List (FreeGroup α × List (α × Bool)))
    (c' t' d q A : List (α × Bool)) (N : ℕ),
    e = e₁ ++ ((FreeGroup.mk c', t') :: f) ∧
    FreeGroup.IsReduced (palindrome c' t') ∧
    FreeGroup.mk d = conjEval e₁ * FreeGroup.mk c' ∧
    c = d ++ q ∧ q <+: t' ∧
    FreeGroup.invRev E <+: t'.rotate q.length ∧
    (conjEval e).toWord
      = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N ∧
    N ≤ c'.length + E.length ∧
    M.length + N ≤ A.length + c'.length + E.length

/-- **The effective conjugator costs nothing.**  A caller never has to invent
`d`: the reduced word of the product always serves, by
`GreendlingerCoincidence.exists_effectiveConjugator`'s witness.  This is the
site's intended introduction rule. -/
theorem conjugatorAbsorbedSite_of_canonical [DecidableEq α]
    {c E M c' t' q A : List (α × Bool)}
    {e e₁ f : List (FreeGroup α × List (α × Bool))} {N : ℕ}
    (he : e = e₁ ++ ((FreeGroup.mk c', t') :: f))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hcq : c = (conjEval e₁ * FreeGroup.mk c').toWord ++ q)
    (hq : q <+: t')
    (hintr : FreeGroup.invRev E <+: t'.rotate q.length)
    (hV : (conjEval e).toWord
      = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N)
    (hN : N ≤ c'.length + E.length)
    (hfit : M.length + N ≤ A.length + c'.length + E.length) :
    ConjugatorAbsorbedSite c E M e :=
  ⟨e₁, f, c', t', (conjEval e₁ * FreeGroup.mk c').toWord, q, A, N, he, hredp',
    FreeGroup.mk_toWord, hcq, hq, hintr, hV, hN, hfit⟩

/-- **The cascade decomposition is free at any split.**  Whatever the landing
factor is, the tail word is a survivor followed by that factor's word with a
prefix removed --- this is `GreendlingerCascade.exists_cascade` read at
`k = |e₁|`.  So the content of the site's last three fields is the two
inequalities, not the decomposition they constrain. -/
theorem exists_cascade_split [DecidableEq α]
    (e₁ f : List (FreeGroup α × List (α × Bool))) (c' t' : List (α × Bool)) :
    ∃ (A : List (α × Bool)) (N : ℕ),
      (conjEval (e₁ ++ ((FreeGroup.mk c', t') :: f))).toWord
        = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N := by
  obtain ⟨A, N, hA⟩ :=
    exists_cascade e₁.length (e₁ ++ ((FreeGroup.mk c', t') :: f))
  rw [List.drop_left] at hA
  exact ⟨A, N, hA⟩

/-! ## Case (α), from the descent's own hypotheses -/

/-- **The landing, from the site and minimality alone.**

This is the plumbing.  `landsIn_of_conjugatorAbsorbed` wants the landing
factor's symmetrization, its minimality, the count that makes the descent
terminate, and the distinctness that turns the intrusion into a piece; every one
of the four comes out of `hmin` and the site alone, so the (α) branch consumes
exactly what `CascadeLanding` hands it. -/
theorem landsIn_of_conjugatorAbsorbedSite [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c t E M : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R) (hEt : E <:+ t)
    (hsite : ConjugatorAbsorbedSite c E M e) :
    LandsIn R M.length (conjEval e).toWord e.length := by
  obtain ⟨e₁, f, c', t', d, q, A, N, he, hredp', hd, hcq, hq, hintr, hV, hN,
    hfit⟩ := hsite
  subst he
  have ht' : t' ∈ symmetrization R := hmin.1 (FreeGroup.mk c', t') (by simp)
  have hdrop :
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c', t') :: f))).drop
        (e₁.length + 1) = (FreeGroup.mk c', t') :: f := by
    rw [List.drop_succ_cons, List.drop_left]
  have hmin' := isMinimalConjExpr_drop (e₁.length + 1)
    ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c', t') :: f))) g hmin
  rw [hdrop] at hmin'
  have hf : f.length < (e₁ ++ ((FreeGroup.mk c', t') :: f)).length := by
    simp only [List.length_append, List.length_cons]
    omega
  exact landsIn_of_conjugatorAbsorbed hmetric ht ht' hEt hintr
    (invRev_ne_rotate_of_minimal hmin hd hcq hq) hf hV hredp' hmin' hN hfit

/-- **The (α) disjunct of `CascadeLanding`, in the descent's own context.**  The
landing side of the disjunction, for a head whose block fits and whose landing
site is conjugator-absorbed. -/
theorem cascadeLanding_of_conjugatorAbsorbedSite [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c t E M P' B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {j : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R) (hEt : E <:+ t)
    (hle : M.length + j ≤ c.length + t.length)
    (hsite : ConjugatorAbsorbedSite c E M e) :
    GreendlingerAt R (c.length + j) (P' ++ B') ∨
      (M.length + j ≤ c.length + t.length ∧
        LandsIn R M.length (conjEval e).toWord e.length) :=
  Or.inr ⟨hle, landsIn_of_conjugatorAbsorbedSite hmetric hmin ht hEt hsite⟩

/-! ## The residual, over the (β) regime only -/

/-- **The landing obligation, (β) only.**  `LandingProduction` with the
orientation package supplied --- the relator segment `E`, its two
decompositions, its position in the head rotation and its nonemptiness, all free
from `eaten_prefix_orientation` --- and with the hypothesis that no
conjugator-absorbed site exists.

The last hypothesis is what makes this a genuine reduction rather than a
restatement: an instance carrying a site is discharged by
`landsIn_of_conjugatorAbsorbedSite`, so the predicate is asked only about the
regime where conjugator letters reach the landing factor's relator letters,
which is where pieces bound nothing and where the design note puts the risk of
the lane. -/
def LandingProductionBeta [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' E : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → 6 * j < t.length →
    M.length + j ≤ c.length + t.length →
    M = E ++ FreeGroup.invRev c →
    FreeGroup.invRev M = c ++ FreeGroup.invRev E →
    E <:+ t → 0 < E.length →
    ¬ConjugatorAbsorbedSite c E M e →
    LandsIn R M.length (conjEval e).toWord e.length

/-- **The landing production, with case (α) discharged.**  The case split is on
the existence of the site; the positive branch is the plumbing above and the
negative branch is the residual predicate. -/
theorem landingProduction_of_beta [DecidableEq α] {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hbeta : LandingProductionBeta R) : LandingProduction R := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj hle
  obtain ⟨E, hM, hMinv, hEt, -, hEpos⟩ :=
    eaten_prefix_orientation heq hlow (by omega)
  by_cases hsite : ConjugatorAbsorbedSite c E M e
  · exact landsIn_of_conjugatorAbsorbedSite hmetric hmin ht hEt hsite
  · exact hbeta c t e g P' M B' E j hmin ht hredp heq htail hlow hj hle hM hMinv
      hEt hEpos hsite

/-- **`CascadeLanding` over (β)-side residuals only.**  The two obligations left
are the deep arc and the landing production outside the conjugator-absorbed
regime; case (α) contributes nothing to the hypothesis, having been discharged
against the descent's own context. -/
theorem cascadeLanding_of_deepArc_of_beta [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    (hdeep : DeepArcSource R) (hbeta : LandingProductionBeta R) :
    CascadeLanding R :=
  cascadeLanding_of_deepArc_of_landing hdeep
    (landingProduction_of_beta hmetric hbeta)

/-- **The gate, over (β)-side residuals only.**  Every nonempty reduced word in
the normal closure of a `C'(1/6)` family whose deep arc produces a located
subword and whose blocks land outside the conjugator-absorbed regime contains
more than half of a symmetrized relator.

This supersedes the two-obligation gate of `GreendlingerBetaBranch` in the sense
that matters for the lane: its landing hypothesis is asked about strictly fewer
instances. -/
theorem greendlingerConclusion_of_deepArc_of_beta [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hdeep : DeepArcSource R) (hbeta : LandingProductionBeta R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_cascadeLanding hR hRne
    (cascadeLanding_of_deepArc_of_beta hmetric hdeep hbeta)

end SmallCancellationRouter
end GroupApproximation
