import GroupApproximation.Sofic.GreendlingerDeepVacuitySharp
import GroupApproximation.Sofic.AvatarMetricCheck

/-!
# The sharp gate from the two live residuals, and its router consumption

Every step between the open mathematics and the router's output is now a
theorem.  This file is the last link: it bundles the two residual families the
lane is actually proving, turns them into
`GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)`, and hands that to the
consumption points, so that the moment the residuals land the router output is
one application and no signature anywhere has to move.

## The two residuals

`SharpResiduals α` has exactly two fields, quantified over every family the gate
is asked about:

* `deep` --- `GreendlingerDeepVacuitySharp.DeepOverrunArcSharp`, the `λ`-twin of
  the overrun obligation `GreendlingerDeepVacuity` reduces the deep side to;
* `beta` --- `GreendlingerSharpTwins.LandingProductionBetaSharp'`, the landing
  obligation `GreendlingerAlphaPlumb` leaves after discharging the
  conjugator-absorbed case, in the disjunctive form: the prover may answer with
  the head factor's located subword instead of a landing site.  The
  non-disjunctive form is very likely false --- `GreendlingerLandingProd`'s
  `ne_nil_of_landingProductionBetaSharp` is a falsification handle at a
  one-factor tail --- and the configuration that kills it is precisely the one
  where the head factor's survivor is the arc, so widening the conclusion costs
  the lane nothing it could have had.

Nothing else is open.  Both fields may assume `∀ r ∈ R, r ≠ []` and `0 < lam`
alongside cyclic reducedness and `C'(λ)`, because
`GreendlingerSharpTwins.sharpGreendlingerGate_of_cascadeLandingSharp` derives
both from the metric condition before it calls the family --- the first through
the empty piece, the second through `lam_pos_of_metric`.  That is the interface
note `GreendlingerDeepVacuitySharp` records: `not_deep_confined` needs the
nonemptiness, and the assembly has already paid for it.

It is a structure rather than two loose binders so that every signature below
carries one hypothesis instead of a dozen lines of quantifier, and so that the
residual provers have a single named target.  All fields are propositions, so
the bundle is itself a `Prop` and is eliminated only into `Prop`; the data at
the far end (`routerData_of_residuals`) comes from the router's own choice
step, exactly as it does for `routerData_of_sharpGate`.

## The chain, in one line each

    SharpResiduals α
      → CascadeLandingSharp family   (cascadeLandingSharp_family_of_sharpResiduals)
      → SharpGreendlingerGate α      (sharpGate_of_residuals)
      → D.RouterConclusions          (routerConclusions_of_residuals)
      → RoutingLemmaData E N s B     (routerData_of_residuals)

The deep half costs only the overrun obligation, because
`GreendlingerDeepVacuitySharp.deepArcSourceSharp_of_deepOverrunArcSharp`
discharges the confined branch against `not_deep_confined`; the landing half
costs only the (β) regime, because
`GreendlingerSharpTwins.landingProductionSharp_of_betaSharp` discharges the
conjugator-absorbed branch against the `λ`-free plumbing.  So the pair below is
the whole of what is left of the free-group half of the router.

Unconditional except where `SharpResiduals` is named.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

/-! ## 1.  The residual bundle -/

/-- **The two residual families of the sharp lane.**  A witness of this is
exactly what the free-group half of the router still owes, and the fields are
stated at the constant the consuming family carries rather than at `1/6`.

Both fields receive `∀ r ∈ R, r ≠ []` and `0 < lam` because the gate assembly
proves them before calling the family; a prover of either field may use them
freely and does not have to re-derive them. -/
structure SharpResiduals (α : Type*) [DecidableEq α] : Prop where
  /-- The deep side: the head's block runs past the whole adjacent palindrome
  and the located conclusion at the sharp bound comes from the tail. -/
  deep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
    0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
    DeepOverrunArcSharp R lam
  /-- The landing side, outside the conjugator-absorbed regime, in the
  **disjunctive** form: the prover may answer with the head factor's located
  subword instead of a landing site.  The non-disjunctive form is very likely
  false in the nonempty-overhang regime --- see §10 of
  `GreendlingerSharpTwins` --- and is exactly the configuration where the head
  factor supplies the arc, so the disjunction is not a weakening of the lane's
  ambition, only of a hypothesis that could not have been met. -/
  beta : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
    0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
    LandingProductionBetaSharp' R lam

/-! ## 2.  The gate -/

/-- **The `CascadeLandingSharp` family, from the bundle.**  One inequality
decides which residual is called and each is stated over the regime it owns;
this is `cascadeLandingSharp_of_deepOverrunArcSharp_of_betaSharp` read at every
family at once, in the shape the gate assembly consumes. -/
theorem cascadeLandingSharp_family_of_sharpResiduals {α : Type*} [DecidableEq α]
    (h : SharpResiduals α) :
    ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam :=
  fun R lam hcyc hRne hlam0 hlam hmetric =>
    cascadeLandingSharp_of_deepArcSharp_of_betaSharp' hmetric
      (deepArcSourceSharp_of_deepOverrunArcSharp hlam hcyc hRne hmetric
        (h.deep R lam hcyc hRne hlam0 hlam hmetric))
      (h.beta R lam hcyc hRne hlam0 hlam hmetric)

/-- **The sharp gate, from the two residuals and nothing else.**

Every side condition a gate could have been asked for is discharged upstream:
nondegeneracy by `exists_two_distinct_symmetrization`, `0 < lam` and
`∀ r ∈ R, r ≠ []` by the empty piece, the degenerate all-empty family by the
trivial normal closure, and the two `λ`-free case splits by
`GreendlingerAlphaPlumb` and `GreendlingerDeepVacuity`.  What is left is the
bundle. -/
theorem sharpGate_of_residuals {α : Type*} [DecidableEq α]
    (h : SharpResiduals α) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_cascadeLandingSharp
    (cascadeLandingSharp_family_of_sharpResiduals h)

/-- The gate on the router's own alphabet, which is the instance every
construction in this repository consumes. -/
theorem sharpGate_fin_two_of_residuals (h : SharpResiduals (Fin 2)) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGate_of_residuals h

/-- **Torsion-freeness of the presented quotient, from the two residuals.**
The sharp gate's own consumer, spelled at the bundle so that the torsion lane
never has to mention the cascade. -/
theorem torsionFree_of_residuals {α : Type*} [DecidableEq α]
    (h : SharpResiduals α) {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam8 : lam ≤ 1 / 8)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R lam)
    (hnpp : GreendlingerFreeGate.NoProperPower R) :
    IsPowerTorsionFree
      (FreeGroup α ⧸ Subgroup.normalClosure (FreeGroup.mk '' R)) :=
  GreendlingerFreeGate.torsionFree_of_sharpGate (sharpGate_of_residuals h)
    hlam8 hcyc hmetric hnpp

end SmallCancellationRouter

/-! ## 3.  The router's consumption point -/

namespace BespokeRouter

open SmallCancellationRouter

namespace RouterRelatorDesign

variable {E : Type} [Group E] {N : Subgroup E} {s : E} {B : Type} [Group B]
    (D : RouterRelatorDesign E N s B)

/-- **Both word-combinatorial fields of the router interface, from the two
residuals.**  `routerConclusions_of_sharpGate` with the gate supplied, so a
caller who has the bundle needs nothing else about the free-group half.

The design supplies cyclic reducedness, the no-proper-power condition and the
protected ball; the caller supplies the `C'(λ)` proof at `λ ≤ 1/8` and the
bundle. -/
theorem routerConclusions_of_residuals (h : SharpResiduals (Fin 2))
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    D.RouterConclusions :=
  D.routerConclusions_of_sharpGate (sharpGate_of_residuals h) hlam8 hmetric

/-- The router's output from the two residuals. -/
noncomputable def routerData_of_residuals [N.Normal] (h : SharpResiduals (Fin 2))
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    RoutingLemmaData E N s B :=
  D.routerData (D.routerConclusions_of_residuals h hlam8 hmetric)

/-- **The frozen endpoint's hypothesis, from the two residuals.**  Whoever
exhibits a design whose family is `C'(1/8)` has discharged the endpoint at that
source, defect, protected element and partner --- modulo the two residuals, and
nothing else. -/
theorem nonempty_routingLemmaData_of_residuals [N.Normal]
    (h : SharpResiduals (Fin 2)) {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    Nonempty (RoutingLemmaData E N s B) :=
  ⟨D.routerData_of_residuals h hlam8 hmetric⟩

end RouterRelatorDesign
end BespokeRouter

/-! ## 4.  The checked family -/

namespace AvatarMetricCheck

/-- **Both router fields at the checked family, from the two residuals.**  The
metric check supplies `C'(1/8)` on the nose, so this is the composition with no
constant to choose: a design whose relators pass the check and a witness of the
bundle give the router's word-combinatorial obligations outright. -/
theorem routerConclusions_of_check_of_residuals {E : Type} [Group E]
    {N : Subgroup E} {s : E} {B : Type} [Group B]
    (D : BespokeRouter.RouterRelatorDesign E N s B)
    (C : AvatarMetricData) (hrel : D.relators = C.relators)
    (h : SmallCancellationRouter.SharpResiduals (Fin 2)) :
    D.RouterConclusions :=
  routerConclusions_of_check D C hrel
    (SmallCancellationRouter.sharpGate_of_residuals h)

/-- **The endpoint at the checked family, from the two residuals.**  The last
line of the lane: a checked design plus the bundle produces the frozen router
output, and the bundle is the only thing still open. -/
theorem nonempty_routingLemmaData_of_check_of_residuals {E : Type} [Group E]
    {N : Subgroup E} [N.Normal] {s : E} {B : Type} [Group B]
    (D : BespokeRouter.RouterRelatorDesign E N s B)
    (C : AvatarMetricData) (hrel : D.relators = C.relators)
    (h : SmallCancellationRouter.SharpResiduals (Fin 2)) :
    Nonempty (SmallCancellationRouter.RoutingLemmaData E N s B) :=
  nonempty_routingLemmaData_of_check D C hrel
    (SmallCancellationRouter.sharpGate_of_residuals h)

end AvatarMetricCheck

end GroupApproximation
