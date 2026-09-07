import GroupApproximation.CharClass.ThomBridgeChartHom
import GroupApproximation.CharClass.ThomBridgeTotalNatural
import GroupApproximation.CharClass.RelativeSubspaceIso

/-!
# The bridge commutes with `relToAbs`

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomBridgeTotal` recorded, in its own docstring, that `bridgeTotal` is published
as a bare isomorphism with nothing relating it to the maps around it, and that
this is a defect for any consumer who has to **compute** across it.  `hclass` is
such a consumer: the Thom class is named on the vector-bundle pair and its
Leray--Hirsch coordinates are read on the projectivisation pair, so the two
descriptions of `j^*` have to be compared.

They are compared by two naturality squares and nothing else.  `bridgeTotal` is,
by `bridgeChart_hom_eq`, the inverse of a single `relPullback` along the chart
inclusion, followed by a `relPullback` along the **identity** that shrinks the
subspace from the complement of the zero section to the hyperplane.  `relToAbs`
is natural for both, and the second square's ambient pullback is the identity.
So the relative-to-absolute image of a class on the vector-bundle pair is the
restriction, to the affine chart, of the relative-to-absolute image of its
partner on the projectivisation pair.

## What this does not do

It relates the two `relToAbs`; it says nothing about `absToSub`, about the
connecting map, or about naturality of the bridge in the base — that last is
`ThomBridgeTotalNatural`'s `bridgeTotal_natural`, a different square.  And it
computes nothing: the Leray--Hirsch expansion of the right-hand side is the
consumer's work.

## Main declarations

* `relToAbs_bridgeTotal` — **the square**.

The chart inclusion's map-of-pairs fact is a `have` inside that proof rather than
a named lemma: lane `lix-hres`'s `ThomChartSquare.bridgeChartIncl_mapsTo` is the
same statement, and two copies under one name would be a duplicate declaration.
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

open ThomChernDeg RelativeSupport

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `pull` is the ambient pullback of a map of pairs, on the nose. -/
theorem pull_eq_absPull {Z W : TopCat.{0}} (f : Z ⟶ W) (n : ℕ) (a : Hmod2 W n) :
    pull f n a = (absPull f n).hom a := rfl

/-- **The bridge commutes with `relToAbs`.**  The relative-to-absolute image of a
class of the vector-bundle pair is the restriction to the affine chart of the
relative-to-absolute image of the class it becomes on the projectivisation pair.

Two applications of `relToAbs_naturality`: one along the chart inclusion, whose
`relPullback` is `bridgeChart` by `bridgeChart_hom_eq`, and one along the
identity of `P(p ⊕ 1)`, whose ambient pullback is the identity. -/
theorem relToAbs_bridgeTotal [CompactSpace X] [T2Space X] (p : Bundle X ι) (n : ℕ)
    (u : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    (relToAbs (ZMod 2) (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n).hom u
      = pull (cmap (bridgeChartIncl p)) n
          ((relToAbs (ZMod 2) (TopCat.of (Bundle.Proj p.plusOne))
            (Set.range (Bundle.projIncl p)) n).hom (bridgeTotal p n u)) := by
  have hA : ∀ v ∈ ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet p),
      (ConcreteCategory.hom (cmap (bridgeChartIncl p))) v
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)) := by
    intro v hv
    have hmem : (((Bundle.chartOpensHomeoTotal p)
        ((Bundle.chartOpensHomeoTotal p).symm v) : Bundle.Total p) : X × (ι → ℂ))
        ∈ Bundle.puncturedSet p := by
      rw [(Bundle.chartOpensHomeoTotal p).apply_symm_apply]
      exact hv
    exact (Bundle.chartOpensHomeoTotal_mem_puncturedSet p
      ((Bundle.chartOpensHomeoTotal p).symm v)).mp hmem
  have hid := (bridgeChart p n).inv_hom_id
  have hu : ((bridgeChart p n).hom).hom ((bridgeChart p n).inv.hom u) = u := by
    have h := congrArg (fun t => t.hom u) hid
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_id, LinearMap.id_coe, id_eq] at h
    exact h
  -- square one: the chart inclusion
  have hsq1 := relToAbs_naturality (ZMod 2) (cmap (bridgeChartIncl p)) hA n
  have hnat1 := congrArg (fun t => t.hom ((bridgeChart p n).inv.hom u)) hsq1
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hnat1
  rw [bridgeChart_hom_eq p n hA] at hu
  rw [hu] at hnat1
  -- square two: the identity of `P(p ⊕ 1)`, shrinking the subspace
  have hsq2 := relToAbs_naturality (ZMod 2) (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
    (A := (Set.range (Bundle.projIncl p) : Set ↥(TopCat.of (Bundle.Proj p.plusOne))))
    (B := ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
      : Set (Bundle.Proj p.plusOne)))
    (fun _ hx => range_projIncl_subset_notZero p hx) n
  have hnat2 := congrArg (fun t => t.hom ((bridgeChart p n).inv.hom u)) hsq2
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    absPull_id_apply] at hnat2
  -- Join the two squares inside the hypothesis, never inside the goal: rewriting
  -- the goal with `hnat2` has to abstract over the map-of-pairs proof carried by
  -- `relPullback`, and the abstraction is not type-correct at `instances`
  -- transparency.  Rewriting `hnat1` instead touches no dependent argument.
  rw [hnat2] at hnat1
  rw [pull_eq_absPull, bridgeTotal_apply]
  exact hnat1.symm

/-! Printed on every build. -/

#print axioms relToAbs_bridgeTotal

end

end GroupApproximation.CharClass
