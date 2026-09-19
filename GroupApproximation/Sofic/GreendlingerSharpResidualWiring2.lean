import GroupApproximation.Sofic.GreendlingerLandingProd
import GroupApproximation.Sofic.GreendlingerDeepVacuitySharp
import GroupApproximation.Sofic.AvatarMetricCheck

/-!
# The sharp gate from the *shorter* pair of residuals, and its router consumption

`Sofic.GreendlingerSharpResidualWiring` bundles the residuals the lane started
from: the deep overrun obligation and the (β) landing production.  This file
bundles the pair the lane will actually prove, and the difference is the landing
half.

`GreendlingerLandingProd` takes `LandingProductionBetaSharp` off the path.  The
landing obligation asks for a landing **site** at every head; the disjunction
`CascadeLandingSharp` actually states asks only for a located subword, and in
the shallow regime the head factor supplies one from its own rotation as soon as
the segment it lost is a piece — the head conjugator's overhang never entering,
because the argument does not look at the landing factor at all.  What is left
is `DeepSegmentDichotomy`: in the (β) regime the deep segment is a piece **or**
the block lands.  Each disjunct is asked exactly where it is true — the overhang
configuration puts the segment along the landing factor's *rotation*, where it
is a piece; the buried configuration puts it along that factor's *conjugator*,
where it is no piece but the block has stopped inside `c'` and
`landsInSharp_of_confined` supplies the landing at offset zero.

That matters for this file because the dichotomy is strictly weaker than the
landing half of `Sofic.GreendlingerSharpResidualWiring`'s bundle:
`GreendlingerLandingProd.deepSegmentDichotomy_of_landingProductionBetaSharp`
proves `LandingProductionBetaSharp → DeepSegmentDichotomy` by reading the
landing obligation at offset `j = 0`, and
`GreendlingerLandingProd.deepSegmentDichotomy_of_deepSegmentIsPiece` proves it
from the other side.  Meanwhile `GreendlingerSharpTwins`'s §10 records why that
landing half is very likely unprovable as stated.  So the two wirings stand in a
definite relation rather than competing: the first is the literal target, this
one is the reachable one, and nothing downstream of either has to know which was
used.

The bundle-level implication `SharpResiduals → SharpResiduals₂` is deliberately
*not* stated here, because it would make this file import the first wiring and
so stop the two from being independent.  Its content is the field-level theorem
named above; a caller holding the older bundle applies that to its `beta` field.

## Two bundles, and which to attack

`GreendlingerLandingProd` §8 pushes the shallow residual one step further still,
so this file carries **two** bundles rather than one:

    SharpResiduals₂ = deep + DeepSegmentDichotomy
    SharpResiduals₃ = deep + LargeSegmentLands          ← the one to attack

with `sharpResiduals₃_of_sharpResiduals₂` in that direction only.
`LargeSegmentLands` is the dichotomy with the piece disjunct replaced by its
negation as a hypothesis: it owes an answer only where the head has lost at
least `λ` of its rotation, since below that threshold
`greendlingerAtSharp_of_two_pieces` fires on the orientation package alone.  It
is the weakest statement anyone has reduced the (β) side to, so it is what the
lane should aim at; `SharpResiduals₂` is kept because it is what the shorter
route was first stated over and because the implication is worth having on the
record.

## The chain, in one line each

    SharpResiduals₂ α
      → CascadeLandingSharp family  (cascadeLandingSharp_family_of_sharpResiduals₂)
      → SharpGreendlingerGate α     (sharpGate_of_residuals₂)
      → D.RouterConclusions          (routerConclusions_of_residuals₂)
      → RoutingLemmaData E N s B     (routerData_of_residuals₂)

    SharpResiduals₃ α
      → SharpGreendlingerGate α      (sharpGate_of_residuals₃)
      → D.RouterConclusions          (routerConclusions_of_residuals₃)
      → Nonempty RoutingLemmaData
                    (nonempty_routingLemmaData_of_check_of_residuals₃)

Every name here carries a `₂` or a `₃` so that both wirings can be imported at
once; they declare no name in common with
`Sofic.GreendlingerSharpResidualWiring`.

Unconditional except where `SharpResiduals₂` and `SharpResiduals₃` are named.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

/-! ## 1.  The shorter residual bundle -/

/-- **The two residuals of the shorter route.**  The deep half is unchanged from
`SharpResiduals`; the landing half is `DeepSegmentDichotomy`, which replaces
`LandingProductionBetaSharp` in the assembly rather than proving it.

Both fields receive cyclic reducedness, `∀ r ∈ R, r ≠ []` and `0 < lam`
alongside `C'(λ)`, because
`GreendlingerSharpTwins.sharpGreendlingerGate_of_cascadeLandingSharp` derives
the last two from the metric condition before it calls the family.  The
dichotomy itself needs neither, so the bundle it is handed is strictly more than
this route consumes; the prefix is kept uniform with the deep half so that one
shape serves both fields. -/
structure SharpResiduals₂ (α : Type*) [DecidableEq α] : Prop where
  /-- The deep side: the head's block runs past the whole adjacent palindrome
  and the located conclusion at the sharp bound comes from the tail. -/
  deep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
    0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
    DeepOverrunArcSharp R lam
  /-- The shallow side, outside the conjugator-absorbed regime: the deep segment
  is a piece, or the block lands. -/
  dich : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
    0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
    DeepSegmentDichotomy R lam

/-! ## 2.  The gate -/

/-- **The `CascadeLandingSharp` family, from the shorter bundle.**  The deep
half goes through `deepArcSourceSharp_of_deepOverrunArcSharp`, which discharges
the confined branch against `not_deep_confined`; the shallow half is the
dichotomy, and the (α) regime is discharged inside
`cascadeLandingSharp_of_deepArcSharp_of_deepSegmentDichotomy`. -/
theorem cascadeLandingSharp_family_of_sharpResiduals₂ {α : Type*}
    [DecidableEq α] (h : SharpResiduals₂ α) :
    ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam :=
  fun R lam hcyc hRne hlam0 hlam hmetric =>
    cascadeLandingSharp_of_deepArcSharp_of_deepSegmentDichotomy hlam hmetric
      (deepArcSourceSharp_of_deepOverrunArcSharp hlam hcyc hRne hmetric
        (h.deep R lam hcyc hRne hlam0 hlam hmetric))
      (h.dich R lam hcyc hRne hlam0 hlam hmetric)

/-- **The sharp gate, from the two residuals of the shorter route and nothing
else.**  Every side condition is discharged upstream: nondegeneracy by
`exists_two_distinct_symmetrization`, `0 < lam` and `∀ r ∈ R, r ≠ []` by the
empty piece, the degenerate all-empty family by the trivial normal closure, and
the two `λ`-free case splits by `GreendlingerAlphaPlumb` and
`GreendlingerDeepVacuity`.  What is left is the bundle. -/
theorem sharpGate_of_residuals₂ {α : Type*} [DecidableEq α]
    (h : SharpResiduals₂ α) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_cascadeLandingSharp
    (cascadeLandingSharp_family_of_sharpResiduals₂ h)

/-- The gate on the router's own alphabet, which is the instance every
construction in this repository consumes. -/
theorem sharpGate_fin_two_of_residuals₂ (h : SharpResiduals₂ (Fin 2)) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGate_of_residuals₂ h

/-- **Torsion-freeness of the presented quotient, from the shorter bundle.**
The sharp gate's own consumer, spelled at the bundle so that the torsion lane
never has to mention the cascade. -/
theorem torsionFree_of_residuals₂ {α : Type*} [DecidableEq α]
    (h : SharpResiduals₂ α) {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam8 : lam ≤ 1 / 8)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R lam)
    (hnpp : GreendlingerFreeGate.NoProperPower R) :
    IsPowerTorsionFree
      (FreeGroup α ⧸ Subgroup.normalClosure (FreeGroup.mk '' R)) :=
  GreendlingerFreeGate.torsionFree_of_sharpGate (sharpGate_of_residuals₂ h)
    hlam8 hcyc hmetric hnpp

/-! ## 2b.  The weakest bundle: the restricted residual

`GreendlingerLandingProd` §8 carries the chain of strengths one step further:

    DeepSegmentDichotomy  →  LargeSegmentLands  →  LandingProductionBetaSharp'

the first implication by contradiction on the piece bound
(`largeSegmentLands_of_deepSegmentDichotomy`), the second by a case split on
`|E|` (`landingProductionBetaSharp'_of_largeSegmentLands`).  `LargeSegmentLands`
is the weakest of the three: it is the dichotomy with the piece disjunct
replaced by its negation as a *hypothesis*, so it owes an answer only where the
head has already lost at least `λ` of its rotation and therefore cannot answer
for itself.  Below that threshold `greendlingerAtSharp_of_two_pieces` fires on
the orientation package alone.

`SharpResiduals₃` is the bundle at that point, and it is the one to attack.
`sharpResiduals₃_of_sharpResiduals₂` records that it is no harder than
`SharpResiduals₂`; the reverse does not hold and is not claimed. -/

/-- **The two residuals at the weakest point.**  The deep half is unchanged; the
shallow half is `LargeSegmentLands`, which owes an answer only when the head has
lost at least `λ` of its rotation. -/
structure SharpResiduals₃ (α : Type*) [DecidableEq α] : Prop where
  /-- The deep side, as in `SharpResiduals₂`. -/
  deep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
    0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
    DeepOverrunArcSharp R lam
  /-- The shallow side: a badly damaged head must land. -/
  large : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
    0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
    LargeSegmentLands R lam

/-- **The dichotomy bundle yields the restricted one.**  The deep halves agree
and `largeSegmentLands_of_deepSegmentDichotomy` supplies the shallow half, using
the metric condition the family prefix already carries.  So aiming at
`SharpResiduals₃` costs the lane nothing it had at `SharpResiduals₂`. -/
theorem sharpResiduals₃_of_sharpResiduals₂ {α : Type*} [DecidableEq α]
    (h : SharpResiduals₂ α) : SharpResiduals₃ α where
  deep := h.deep
  large := fun R lam hcyc hRne hlam0 hlam hmetric =>
    largeSegmentLands_of_deepSegmentDichotomy hmetric
      (h.dich R lam hcyc hRne hlam0 hlam hmetric)

/-- **The sharp gate from the weakest bundle.**  The deep half goes through
`deepArcSourceSharp_of_deepOverrunArcSharp`; the shallow half is handed to
`sharpGreendlingerGate_of_deepArcSharp_of_largeSegmentLands`, which routes
through the disjunctive obligation of `GreendlingerSharpTwins` §10. -/
theorem sharpGate_of_residuals₃ {α : Type*} [DecidableEq α]
    (h : SharpResiduals₃ α) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_deepArcSharp_of_largeSegmentLands
    (fun R lam hcyc hRne hlam0 hlam hmetric =>
      deepArcSourceSharp_of_deepOverrunArcSharp hlam hcyc hRne hmetric
        (h.deep R lam hcyc hRne hlam0 hlam hmetric))
    h.large

/-- The gate on the router's own alphabet, from the weakest bundle. -/
theorem sharpGate_fin_two_of_residuals₃ (h : SharpResiduals₃ (Fin 2)) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGate_of_residuals₃ h

/-- Torsion-freeness of the presented quotient, from the weakest bundle. -/
theorem torsionFree_of_residuals₃ {α : Type*} [DecidableEq α]
    (h : SharpResiduals₃ α) {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam8 : lam ≤ 1 / 8)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R lam)
    (hnpp : GreendlingerFreeGate.NoProperPower R) :
    IsPowerTorsionFree
      (FreeGroup α ⧸ Subgroup.normalClosure (FreeGroup.mk '' R)) :=
  GreendlingerFreeGate.torsionFree_of_sharpGate (sharpGate_of_residuals₃ h)
    hlam8 hcyc hmetric hnpp

end SmallCancellationRouter

/-! ## 3.  The router's consumption point -/

namespace BespokeRouter

open SmallCancellationRouter

namespace RouterRelatorDesign

variable {E : Type} [Group E] {N : Subgroup E} {s : E} {B : Type} [Group B]
    (D : RouterRelatorDesign E N s B)

/-- **Both word-combinatorial fields of the router interface, from the shorter
bundle.**  `routerConclusions_of_sharpGate` with the gate supplied, so a caller
who has the bundle needs nothing else about the free-group half. -/
theorem routerConclusions_of_residuals₂ (h : SharpResiduals₂ (Fin 2))
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    D.RouterConclusions :=
  D.routerConclusions_of_sharpGate (sharpGate_of_residuals₂ h) hlam8 hmetric

/-- Both word-combinatorial fields of the router interface, from the weakest
bundle. -/
theorem routerConclusions_of_residuals₃ (h : SharpResiduals₃ (Fin 2))
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    D.RouterConclusions :=
  D.routerConclusions_of_sharpGate (sharpGate_of_residuals₃ h) hlam8 hmetric

/-- The router's output from the shorter bundle. -/
noncomputable def routerData_of_residuals₂ [N.Normal]
    (h : SharpResiduals₂ (Fin 2)) {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    RoutingLemmaData E N s B :=
  D.routerData (D.routerConclusions_of_residuals₂ h hlam8 hmetric)

/-- **The frozen endpoint's hypothesis, from the shorter bundle.**  Whoever
exhibits a design whose family is `C'(1/8)` has discharged the endpoint at that
source, defect, protected element and partner --- modulo the two residuals, and
nothing else. -/
theorem nonempty_routingLemmaData_of_residuals₂ [N.Normal]
    (h : SharpResiduals₂ (Fin 2)) {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    Nonempty (RoutingLemmaData E N s B) :=
  ⟨D.routerData_of_residuals₂ h hlam8 hmetric⟩

end RouterRelatorDesign
end BespokeRouter

/-! ## 4.  The checked family -/

namespace AvatarMetricCheck

/-- **Both router fields at the checked family, from the shorter bundle.**  The
metric check supplies `C'(1/8)` on the nose, so this is the composition with no
constant to choose. -/
theorem routerConclusions_of_check_of_residuals₂ {E : Type} [Group E]
    {N : Subgroup E} {s : E} {B : Type} [Group B]
    (D : BespokeRouter.RouterRelatorDesign E N s B)
    (C : AvatarMetricData) (hrel : D.relators = C.relators)
    (h : SmallCancellationRouter.SharpResiduals₂ (Fin 2)) :
    D.RouterConclusions :=
  routerConclusions_of_check D C hrel
    (SmallCancellationRouter.sharpGate_of_residuals₂ h)

/-- **The endpoint at the checked family, from the shorter bundle.**  The last
line of the lane: a checked design plus the bundle produces the frozen router
output, and the bundle is the only thing still open. -/
theorem nonempty_routingLemmaData_of_check_of_residuals₂ {E : Type} [Group E]
    {N : Subgroup E} [N.Normal] {s : E} {B : Type} [Group B]
    (D : BespokeRouter.RouterRelatorDesign E N s B)
    (C : AvatarMetricData) (hrel : D.relators = C.relators)
    (h : SmallCancellationRouter.SharpResiduals₂ (Fin 2)) :
    Nonempty (SmallCancellationRouter.RoutingLemmaData E N s B) :=
  nonempty_routingLemmaData_of_check D C hrel
    (SmallCancellationRouter.sharpGate_of_residuals₂ h)

/-- **The endpoint at the checked family, from the weakest bundle.**  The last
line of the lane, stated at the point the lane is actually attacking: a checked
design plus `SharpResiduals₃` produces the frozen router output, and that bundle
is the only thing still open.

The remaining consumers at `SharpResiduals₃` are each one line from
`sharpGate_of_residuals₃` through the existing `_of_sharpGate` family, so they
are not restated here. -/
theorem nonempty_routingLemmaData_of_check_of_residuals₃ {E : Type} [Group E]
    {N : Subgroup E} [N.Normal] {s : E} {B : Type} [Group B]
    (D : BespokeRouter.RouterRelatorDesign E N s B)
    (C : AvatarMetricData) (hrel : D.relators = C.relators)
    (h : SmallCancellationRouter.SharpResiduals₃ (Fin 2)) :
    Nonempty (SmallCancellationRouter.RoutingLemmaData E N s B) :=
  nonempty_routingLemmaData_of_check D C hrel
    (SmallCancellationRouter.sharpGate_of_residuals₃ h)

end AvatarMetricCheck

end GroupApproximation
