import GroupApproximation.Sofic.GreendlingerSharpRigidity
import GroupApproximation.Sofic.GreendlingerSharpThreeFactor
import GroupApproximation.Sofic.GreendlingerSharpDeepArc

/-!
# The sharp induction frame: what the deep lane still owed at an arbitrary `λ`

`GreendlingerDeepInduction` is the frame that carries the three-factor overrun
count to expressions of any length, and most of it is already twinned.
`DeepOverrunLandingSharp`, `deepOverrunArcSharp_of_landingSharp`,
`CascadeLandingDropSharp` and the whole drop-form descent
(`greendlingerAtSharp_drop_of_cascadeLandingDropSharp`,
`greendlingerConclusionSharp_of_cascadeLandingDropSharp`) live in that file
beside their `λ`-free originals; `DeepOverrunLandingTailSharp` and
`deepOverrunLandingSharp_of_depthSharp_of_tailSharp` live in
`GreendlingerSharpThreeFactor`; `DeepArcDropSharp` and
`cascadeLandingDropSharp_of_deepArcDropSharp_of_landingSharp` live in
`GreendlingerDeepInvariant`.

What was left is a short list, and this file is exactly that list.  Nothing
here is new mathematics --- every statement is its `λ`-free counterpart with the
constant moved, and four of the seven are one-line compositions of twins that
already exist.  The point is that the deep lane's end states can now be quoted
at the family's own constant without a caller reassembling them.

## The three shapes that appear

**Impossibilities need no sharpening.**  `GreendlingerDeepVacuity`'s three
junction kills --- `not_hug_overrun`, `not_relator_swallowed`,
`not_deep_confined` --- conclude `False`, so there is no bound in them to move.
Their only `λ`-dependence is the constant the piece bound is read at, and
`GreendlingerDeepVacuitySharp.metricSmallCancellation_of_le` supplies it; where
the offset hypothesis appears, `six_mul_lt_of_lam_lt` casts the sharp form down
to the half form, which is *stronger* below `1/6`.  This is precisely the
recipe `not_deep_two_factor_sharp` follows, and §1 completes the layer with the
other three.

**One real twin.**  `greendlingerAtSharp_drop_of_landing_palindrome` (§2) is the
`λ`-twin of `greendlingerAt_drop_of_landing_palindrome`, the discharge the
weakened invariant runs on: when the tail survivor is a palindrome with `N₃`
letters removed, a further drop of `k` composes with it, and the arc follows
from the total intrusion being a piece.  The sharp version needs `0 ≤ λ` and
`λ ≤ 1/3` --- both from `greendlingerAtSharp_of_landing_start_of_piece`, where
they replace the `λ`-free version's "a sixth is comfortably under a half".

**Three end states.**  §3 and §4 quote the sharp gate over the residual pairs
the deep lane actually owes.  `GreendlingerDeepVacuitySharp` and
`GreendlingerSharpThreeFactor` each stop at `CascadeLandingSharp`; the half-form
file goes one step further to `GreendlingerConclusion`, and these are the twins
of that last step, plus the family-level gate assembly for the depth/tail/(β)
triple.

## What is *not* here, and why

`GreendlingerCascade` is fully twinned already --- `LandsIn`, `CascadeLanding`,
`GreendlingerAt.transport` and the descent all have `Sharp` counterparts in
`GreendlingerSharpTwins` --- and its remaining three theorems (`drop_add`,
`exists_residual_step`, `exists_cascade`) read no constant at all, so a twin
would be the same theorem under a second name.

The same holds for the `λ`-neutral half of `GreendlingerDeepInduction`:
`toWord_conjEval_singleton`, `exists_overrun_landing_drop`,
`exists_palindromic_at`, `exists_palindromic_thd`, `conjEval_cons_congr`,
`conjEval_swap_snd`, the two distance-two reroute pins
(`eaten_le_of_minimal_reroute_two`, `hug_le_of_minimal_reroute_two`, both
stated in norms and lengths with no fraction anywhere), and the structural
layer `LocatedSplit.drop_of_le` / `LocatedSplit.of_suffix` /
`drop_suffix_append`, which is shared by both constants by construction.

Nothing in this file discharges an open residual.  Every theorem below is a
reduction, an adapter, or an impossibility already proved at `1/6`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The junction kills, callable from the sharp lane

Three `False`-valued statements, each proved once in `GreendlingerDeepVacuity`
at `C'(1/6)`.  A sharp caller holds `MetricSmallCancellation R lam` with
`lam ≤ 1/6` and, in the third case, the sharp offset hypothesis; the two
brackets of `GreendlingerDeepVacuitySharp` convert both. -/

/-- **A hug cannot be run out the far end of the rotation it hugs, at any
`λ ≤ 1/6`.**  The sharp-callable form of
`GreendlingerDeepVacuity.not_hug_overrun`.

Every hypothesis except the metric one is `λ`-free, and the conclusion is
`False`, so there is nothing to sharpen: `metricSmallCancellation_of_le` raises
the constant to the one the piece bound inside is read at and the `λ`-free
argument serves verbatim. -/
theorem not_hug_overrun_sharp [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    {c c' q X t t' E : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredc : FreeGroup.IsReduced c) (hredc' : FreeGroup.IsReduced c')
    (hEt : E <:+ t)
    (hcq : c = c' ++ q) (hqX : t' = q ++ X)
    (hX : X <+: FreeGroup.invRev E) : False :=
  not_hug_overrun (metricSmallCancellation_of_le hlam hmetric) hmin ht ht'
    hredc hredc' hEt hcq hqX hX

/-- **A rotation cannot be swallowed by the stretch destroyed out of another,
at any `λ ≤ 1/6`.**  The sharp-callable form of
`GreendlingerDeepVacuity.not_relator_swallowed`, and the same one-bracket
argument as above. -/
theorem not_relator_swallowed_sharp [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    {c t t' y p : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk (c ++ y), t') :: f) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hyp : y ++ p <+: FreeGroup.invRev t)
    (ht'p : t' <+: p) : False :=
  not_relator_swallowed (metricSmallCancellation_of_le hlam hmetric) hmin ht ht'
    hyp ht'p

/-- **The deep regime admits no confined configuration, at any `λ ≤ 1/6`.**
The sharp-callable form of `GreendlingerDeepVacuity.not_deep_confined`, and the
general case of `GreendlingerSharpThreeFactor.not_deep_two_factor_sharp`, which
is this at an empty tail.

Both brackets are spent here: `metricSmallCancellation_of_le` on the constant
and `six_mul_lt_of_lam_lt` on the offset.  The second direction is the one that
matters --- below `1/6` the sharp offset hypothesis `j < λ|t|` is *stronger*
than `6j < |t|`, so a single impossibility argument discharges both forms, and
no converse is needed or available.

`GreendlingerDeepVacuitySharp.deepArcSourceSharp_of_deepOverrunArcSharp` calls
`not_deep_confined` through exactly this pair of brackets, inline; this names
the composite so the deep lane's other consumers need not repeat it. -/
theorem not_deep_confined_sharp [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {j : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + j) : False :=
  not_deep_confined hRne (metricSmallCancellation_of_le hlam hmetric) hmin ht
    ht' hredp hredp' heq heq' hlow (six_mul_lt_of_lam_lt hlam hj) hgt

/-! ## 2.  The landing factor pays for the weakened arc, at an arbitrary `λ` -/

/-- **The sharp twin of
`GreendlingerDeepInduction.greendlingerAt_drop_of_landing_palindrome`.**

When the tail survivor is a palindrome with `N₃` letters removed --- which is
what `exists_overrun_landing_drop` and
`GreendlingerDeepThreeFactor.exists_three_factor_landing_drop` supply --- any
further drop `k` composes with the one already taken, and
`greendlingerAtSharp_of_landing_start_of_piece` produces the arc as soon as the
**total** intrusion `N₃ + k - |c₃|` into that rotation is a piece.

The proof is the `λ`-free one line for line; the two side conditions are the
ones that producer carries.  `0 ≤ λ` is what makes an intrusion under `λ|t₃|`
an intrusion under `3λ|t₃|`, and `λ ≤ 1/3` keeps the sharp arc bound `1 - 3λ`
nonnegative --- together they are the sharp reading of the `λ`-free version's
"a sixth is comfortably under a half".  Both are free in the lane's range,
since it works at `λ ≤ 1/6`.

As there, no ratio between the head and landing rotations is read, no swallow
bound, and no bound on the overrun depth: this is the discharge the *located*
form could not have, because there the arc had to be positioned against a
rotation it knows nothing about. -/
theorem greendlingerAtSharp_drop_of_landing_palindrome
    {R : Set (List (α × Bool))} {lam : ℚ} {c₃ t₃ B' : List (α × Bool)}
    {N₃ k : ℕ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 3)
    (ht₃ : t₃ ∈ symmetrization R)
    (hB' : B' = (palindrome c₃ t₃).drop N₃)
    (hpiece : ((N₃ + k - c₃.length : ℕ) : ℚ) < lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam 0 (B'.drop k) := by
  rw [hB', ← drop_add N₃ k (palindrome c₃ t₃)]
  exact (greendlingerAtSharp_of_landing_start_of_piece hlam0 hlam ht₃
    hpiece).mono (Nat.zero_le _)

/-! ## 3.  The sharp conclusion over the overrun residual

`GreendlingerDeepVacuitySharp` stops at `CascadeLandingSharp`.  The `λ`-free
file goes one step further --- `greendlingerConclusion_of_deepOverrunArc_of_landing`
--- and these are the twins of that step, in both the plain and the (β) form of
the landing side. -/

/-- **The sharp deep obligation in tail form, from the sharp overrun
obligation.**  The `λ`-twin of
`GreendlingerDeepVacuity.deepTailArc_of_deepOverrunArc`.

The sharp lane reaches `DeepArcSourceSharp` directly, in one pass, because
`deepArcSourceSharp_of_deepOverrunArcSharp` folds the tail step into the
five-leaf case analysis.  `GreendlingerSharpDeepArc.deepTailArcSharp_of_deepArcSourceSharp`
is the converse of the missing half, so composing the two recovers the tail
form --- which is the shape `GreendlingerSharpDeepArc`'s own consumers take. -/
theorem deepTailArcSharp_of_deepOverrunArcSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    (h : DeepOverrunArcSharp R lam) : DeepTailArcSharp R lam :=
  deepTailArcSharp_of_deepArcSourceSharp
    (deepArcSourceSharp_of_deepOverrunArcSharp hlam hR hRne hmetric h)

/-- **The sharp gate, reduced to the overrun obligation and the landing
production.**  The `λ`-twin of
`GreendlingerDeepVacuity.greendlingerConclusion_of_deepOverrunArc_of_landing`.

The deep branch of `CascadeLandingSharp` costs exactly one statement about
blocks that reach past the factor next to them, and this is that reduction
carried to the gate's own conclusion. -/
theorem greendlingerConclusionSharp_of_deepOverrunArcSharp_of_landingSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepOverrunArcSharp R lam)
    (hland : LandingProductionSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingSharp hR hRne hlam0 hlam
    (cascadeLandingSharp_of_deepOverrunArcSharp_of_landingSharp hlam hR hRne
      hmetric hdeep hland)

/-- The same over the (β) form of the landing side, which is the pair the
residual bundle of `GreendlingerSharpResidualWiring` is stated over. -/
theorem greendlingerConclusionSharp_of_deepOverrunArcSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepOverrunArcSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingSharp hR hRne hlam0 hlam
    (cascadeLandingSharp_of_deepOverrunArcSharp_of_betaSharp hlam hR hRne
      hmetric hdeep hbeta)

/-! ## 4.  The deep lane's two residuals, carried to the gate

`GreendlingerSharpThreeFactor.cascadeLandingSharp_of_depthSharp_of_tailSharp_of_betaSharp`
assembles the invariant from the sharp three-factor count, the not-last-factor
landing and the (β) production.  The `λ`-free file carries the same triple to
`GreendlingerConclusion`; these are the twins of that, and of the family-level
gate the routing lane consumes. -/

/-- **The sharp conclusion over the sharp count, the residual and (β).**  The
`λ`-twin of
`GreendlingerDeepInduction.greendlingerConclusion_of_depth_of_tail_of_beta`.

`λ ≤ 1/6` is the lane's own constraint; the `λ ≤ 1/3` the three-factor count
needs is implied by it and is discharged inside
`cascadeLandingSharp_of_depthSharp_of_tailSharp_of_betaSharp`.  `0 < λ` is what
the gate's own conclusion needs, through the untouched-rotation arc producer. -/
theorem greendlingerConclusionSharp_of_depthSharp_of_tailSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdepth : DeepOverrunDepthSharp R lam)
    (htail : DeepOverrunLandingTailSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingSharp hR hRne hlam0 hlam
    (cascadeLandingSharp_of_depthSharp_of_tailSharp_of_betaSharp hlam hR hRne
      hmetric hdepth htail hbeta)

/-- **The sharp gate over the deep lane's three families.**

`SharpGreendlingerGate α` from the sharp three-factor count, the
not-last-factor landing residual and the (β) landing production --- these being
the `λ`-twins of exactly the three statements
`GreendlingerDeepInduction.greendlingerConclusion_of_depth_of_tail_of_beta`
reduces the half-form gate to.

The two side conditions the gate does not supply, `0 < λ` and
`∀ r ∈ R, r ≠ []`, are recovered by
`GreendlingerSharpTwins.sharpGreendlingerGate_of_cascadeLandingSharp` from a
piece of the empty word, and handed on to all three families; the
all-relators-empty branch is refuted there through the trivial normal closure.

All three arguments are hypotheses.  Nothing here discharges any of them. -/
theorem sharpGreendlingerGate_of_depthSharp_of_tailSharp_of_betaSharp
    [DecidableEq α]
    (hdepth : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepOverrunDepthSharp R lam)
    (htail : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepOverrunLandingTailSharp R lam)
    (hbeta : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionBetaSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_cascadeLandingSharp
    fun R lam hcyc hRne hlam0 hlam hmetric =>
      cascadeLandingSharp_of_depthSharp_of_tailSharp_of_betaSharp hlam hcyc hRne
        hmetric (hdepth R lam hcyc hRne hlam0 hlam hmetric)
        (htail R lam hcyc hRne hlam0 hlam hmetric)
        (hbeta R lam hcyc hRne hlam0 hlam hmetric)

/-- The same on the router's own alphabet, which is the instance every
construction in this repository consumes. -/
theorem sharpGreendlingerGate_fin_two_of_depthSharp_of_tailSharp_of_betaSharp
    (hdepth : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepOverrunDepthSharp R lam)
    (htail : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepOverrunLandingTailSharp R lam)
    (hbeta : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionBetaSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_depthSharp_of_tailSharp_of_betaSharp hdepth htail
    hbeta

end SmallCancellationRouter
end GroupApproximation
