import GroupApproximation.GGT.DGOWindmillGrowth
import GroupApproximation.GGT.DGOWindmillExhaust
import GroupApproximation.GGT.DGORotatingQuotientResidual

/-!
# From windmills to DGO's Theorem 5.3(b)

Twelfth module of the campaign aimed at
`Manuscript.NonMF.TheoremCDebts.dgoTheorem53`.

This module packages the endpoint reduction and assembles the windmill
induction into `HullSC.DGOQuotientStatementGeodesic`, the repaired form of
DGO's Theorem 5.3 that the debt row records.  The two named `Prop`s expose the
growth and exhaustion halves of the induction; both receive concrete
constructors below.

## The two obligations

* `WindmillGrowth` --- every windmill is contained in a strictly larger one,
  with a fixed thickness of gain.  This is DGO's Proposition 5.12.  The
  explicit enlarged set and all five windmill clauses are in
  `GGT/DGOWindmillGrowth.lean`.
* `WindmillExhaustion` --- every element of the subgroup the rotations generate
  already lies in the group of *some* windmill.  This follows from
  `WindmillGrowth` by iterating from the ball of radius `100δ` about one apex
  until the windmills swallow any given apex.

## Why the last step is three lines

Because the windmill's fifth axiom was chosen to be the conclusion the debt row
asks for.  Once an element is inside some `G_W`, the axiom hands back either a
rotation at an apex of `W` --- which is the first disjunct of
`HullSC.RotatingQuotient.rotation_or_loxodromic` with conjugator `1` --- or
`IsLoxodromic` at one basepoint, which `isLoxodromic_of_isLoxodromic` moves to
every basepoint.  Nothing else is needed, and in particular the identity needs no
special handling: `IsWindmill.dichotomy` is stated for *every* element of `G_W`,
including `1`, because `apex_mem` guarantees an apex whose rotation subgroup
contains it.  That is why the restriction `g ≠ 1` in the debt row's statement --
which `HullSC.not_rotation_or_loxodromic_of_empty` shows is necessary there --
never has to be propagated inwards.

## The empty family is handled separately, and must be

With no apices there is no windmill (`IsWindmill.apex_mem` fails), and no
windmill machinery applies.  That is correct rather than a gap: the subgroup the
rotations generate is trivial, so the dichotomy is vacuous, and
`HullSC.rotationNormalClosure_empty` discharges it directly.  This is the same
configuration `HullSC.not_rotation_or_loxodromic_of_empty` uses to refute the
*unrestricted* dichotomy, so it has to be kept outside the induction.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## The two obligations of the induction -/

/-- **DGO's Proposition 5.12**: every windmill grows, by a fixed thickness.

The gain of `10δ` is what makes the iteration exhaust the space; the growth step
actually produces more, but `10δ` is all the exhaustion argument spends. -/
def WindmillGrowth (G : Type u) (X : Type v) [Group G] [PseudoMetricSpace X]
    [MulAction G X] (δ : ℝ) (C : Set X) (Rot : X → Subgroup G) : Prop :=
  ∀ W : Set X, IsWindmill G X δ C Rot W →
    ∃ W' : Set X, IsWindmill G X δ C Rot W' ∧ thicken W (10 * δ) ⊆ W'

/-- **The concrete next-stage construction reduces growth to one windmill
check.**  The `10δ` gain is already a theorem of `DGOWindmillGrowth`; a caller
only has to prove that the explicitly defined `nextWindmill` satisfies the five
fields of `IsWindmill`. -/
theorem windmillGrowth_of_nextWindmill {δ : ℝ} (hδ : 0 < δ) {C : Set X}
    {Rot : X → Subgroup G}
    (hnext : ∀ W : Set X, IsWindmill G X δ C Rot W →
      IsWindmill G X δ C Rot (nextWindmill δ C Rot W)) :
    WindmillGrowth G X δ C Rot := by
  intro W hW
  exact ⟨nextWindmill δ C Rot W, hnext W hW,
    thicken_subset_nextWindmill hδ⟩

/-- **DGO's Proposition 5.12.**  The explicit next windmill gives every
windmill a `10δ` growth stage. -/
theorem windmillGrowth
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 200 * δ ≤ ρ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X)
    {C : Set X} {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) (hsep : IsSeparated C ρ) :
    WindmillGrowth G X δ C Rot :=
  windmillGrowth_of_nextWindmill hδ fun _W hW =>
    isWindmill_nextWindmill hδ hρ hhyp hgeo hfam hvr hsep hW

/-- **The exhaustion**: every element of the subgroup the rotations generate lies
in the group of some windmill.

An element of the rotation closure is a product of finitely many rotations, so
only finitely many apices are involved, and the windmills of the iteration
eventually contain all of them. -/
def WindmillExhaustion (G : Type u) (X : Type v) [Group G] [PseudoMetricSpace X]
    [MulAction G X] (δ : ℝ) (C : Set X) (Rot : X → Subgroup G) : Prop :=
  ∀ g ∈ rotationNormalClosure C Rot,
    ∃ W : Set X, IsWindmill G X δ C Rot W ∧ g ∈ windmillGroup C Rot W

/-- **Growth implies exhaustion.**  Iteration starts from the `100δ` ball
windmill, gains `10δ` at every step, and closure induction uses the increasing
chain to place every finite product of rotations in one windmill group. -/
theorem windmillExhaustion_of_windmillGrowth {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ : 200 * δ ≤ ρ) (hhyp : IsHyperbolicSpace δ X)
    (hgeo : IsGeodesicSpace X) {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) (hsep : IsSeparated C ρ)
    {c₀ : X} (hc₀ : c₀ ∈ C) (hgrow : WindmillGrowth G X δ C Rot) :
    WindmillExhaustion G X δ C Rot :=
  windmillExhaustion_of_growth hδ hρ hhyp hgeo hfam hsep hc₀ hgrow

/-- **The concrete windmill exhaustion.**  Starting at the `100δ` ball about
one apex and iterating the explicit growth step exhausts the rotation
closure. -/
theorem windmillExhaustion {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ : 200 * δ ≤ ρ) (hhyp : IsHyperbolicSpace δ X)
    (hgeo : IsGeodesicSpace X) {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) (hvr : IsVeryRotating G X δ C Rot)
    (hsep : IsSeparated C ρ) {c₀ : X} (hc₀ : c₀ ∈ C) :
    WindmillExhaustion G X δ C Rot :=
  windmillExhaustion_of_windmillGrowth hδ hρ hhyp hgeo hfam hsep hc₀
    (windmillGrowth hδ hρ hhyp hgeo hfam hvr hsep)

/-! ## The dichotomy -/

/-- **The dichotomy of DGO's Theorem 5.3(b), from the exhaustion.**

Every element of the rotation closure sits in some windmill's group, and that
windmill's fifth axiom is the dichotomy.  The rotation branch is returned with
conjugator `1`, and the loxodromic branch is moved from the axiom's existential
basepoint to every basepoint. -/
theorem rotation_or_loxodromic_of_exhaustion {δ : ℝ} {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hexh : WindmillExhaustion G X δ C Rot) :
    ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 →
      (∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c) ∨
        ∀ x : X, IsLoxodromic g x := by
  intro g hg _
  obtain ⟨W, hW, hgW⟩ := hexh g hg
  rcases hW.dichotomy g hgW with ⟨c, hc, -, hgc⟩ | ⟨x, hlox⟩
  · refine Or.inl ⟨1, c, hc, ?_⟩
    rw [inv_one, one_mul, mul_one]
    exact hgc
  · exact Or.inr fun x' => isLoxodromic_of_isLoxodromic hfam.isometric hlox x'

/-- **The conclusion of DGO's Theorem 5.3, from the exhaustion.** -/
theorem nonempty_rotatingQuotient_of_exhaustion {δ : ℝ} {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hexh : WindmillExhaustion G X δ C Rot) :
    Nonempty (RotatingQuotient C Rot) :=
  nonempty_rotatingQuotient_of_dichotomy
    (rotation_or_loxodromic_of_exhaustion hfam hexh)

/-! ## The empty family -/

/-- **With no apices the conclusion is immediate**, the rotation closure being
trivial.

Kept separate because no windmill exists over an empty apex set, and because
this is exactly the configuration at which the *unrestricted* dichotomy is false
(`HullSC.not_rotation_or_loxodromic_of_empty`), so the restriction to `g ≠ 1` is
load-bearing here and nowhere else. -/
theorem nonempty_rotatingQuotient_of_apices_empty {C : Set X}
    (Rot : X → Subgroup G) (hC : C = ∅) :
    Nonempty (RotatingQuotient C Rot) := by
  subst hC
  refine nonempty_rotatingQuotient_of_dichotomy ?_
  intro g hg hg1
  rw [rotationNormalClosure_empty, Subgroup.mem_bot] at hg
  exact absurd hg hg1

/-! ## The statement the debt row records -/

/-- **DGO's Theorem 5.3 in the repaired geodesic form.**  An empty apex family
is immediate.  Otherwise choose one apex, iterate the explicit windmill growth
from its `100δ` ball, and apply the windmill dichotomy to the resulting
exhaustion. -/
theorem dgoQuotientStatementGeodesic :
    DGOQuotientStatementGeodesic.{u, v} := by
  intro G _ X _ _ δ ρ C Rot hδ hρ hhyp hgeo hfam hsep hvr
  by_cases hC : C = ∅
  · exact nonempty_rotatingQuotient_of_apices_empty Rot hC
  · obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.mpr hC
    exact nonempty_rotatingQuotient_of_exhaustion hfam
      (windmillExhaustion hδ hρ hhyp hgeo hfam hvr hsep hc₀)

end DGOWindmill
end GroupApproximation
