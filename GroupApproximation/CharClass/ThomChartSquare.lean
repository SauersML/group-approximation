import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.CharClass.ThomBridgeTotalNatural
import GroupApproximation.CharClass.ThomHyperSquare

/-!
# The chart square, and the Thom bridge's naturality with nothing left to supply

Lane `lix-hres` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomBridgeTotalNatural.bridgeTotal_natural` takes its two squares as arguments,
and `ThomHyperSquare.hyperSquare` discharged the second one at the bundle's own
objects.  This file does the same for the first, so that the bridge's naturality
in the base is a statement about the bundle with no map-of-pairs conditions left
to write at a use site.

The six conditions of `bridgeChart_natural` are all definitional in `cc-bundle`'s
projection model: the chart inclusion lands off the zero section by
`chartOpensHomeoTotal_mem_puncturedSet`, the inclusion of the restricted total
space is a map of punctured pairs by `totalInclOn_mem_puncturedSet_iff`, and the
inclusion of the restricted projectivisation preserves the complement of the zero
section by `projInclOn_mem_notZeroOpensSet_iff`.  The two composite conditions are
those three chained.

**What this does not do.**  It says nothing about restricting to a subset of the
base that is *not* compact Hausdorff: `bridgeTotal` does not exist there, as
`ThomBridgeTotalNatural` records, so `bridgeTotalRestrict` below is stated with
the instances on `↥U` and is unavailable over a ball.  It also says nothing about
the Leray–Hirsch coordinates; that is `ThomJmNatural`.

## Main declarations

* `bridgeChartIncl_mapsTo`, `totalInclOn_mapsTo` — the two map-of-pairs facts.
* `chartSquare` — **the first square**, at the bundle's own objects.
* `bridgeTotalRestrict` — **the bridge is natural in the base**, unconditionally.
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The two map-of-pairs facts -/

omit [DecidableEq ι] in
/-- **The inclusion of the restricted total space is a map of punctured pairs.**
One direction of `cc-bundle`'s membership equivalence. -/
theorem totalInclOn_mapsTo (p : Bundle X ι) (U : Set X) :
    ∀ v ∈ ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet (p.restrictTo U)),
      (ConcreteCategory.hom (cmap (Bundle.totalInclOn p U))) v
        ∈ ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) :=
  fun v hv => (Bundle.totalInclOn_mem_puncturedSet_iff p U v).mpr hv

/-- **The chart inclusion lands off the zero section.**  This is
`bridgeChart_natural`'s first condition; the chart identification is a map of
pairs, so a point of the total space off the zero section has its chart image in
the complement of the zero section. -/
theorem bridgeChartIncl_mapsTo (p : Bundle X ι) :
    ∀ v ∈ ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p),
      (ConcreteCategory.hom (cmap (bridgeChartIncl p))) v
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)) := by
  intro v hv
  show ((Bundle.chartOpensHomeoTotal p).symm v : Bundle.Proj p.plusOne)
      ∈ Bundle.notZeroOpensSet p
  refine (Bundle.chartOpensHomeoTotal_mem_puncturedSet p
    ((Bundle.chartOpensHomeoTotal p).symm v)).mp ?_
  rw [Homeomorph.apply_symm_apply]
  exact hv

/-! ## 2. The chart square -/

/-- **The first two bridge steps are natural in the base, at the bundle's own
objects.**  `bridgeChart_natural` with all six conditions discharged. -/
theorem chartSquare (p : Bundle X ι) (U : Set X) (n : ℕ) :
    (bridgeChart p n).hom
        ≫ relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U))
            (totalInclOn_mapsTo p U) n
      = relPullback (ZMod 2) (cmap (Bundle.projInclOn p.plusOne U))
          (fun z hz => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U z).mpr hz) n
        ≫ (bridgeChart (p.restrictTo U) n).hom :=
  bridgeChart_natural p U n (bridgeChartIncl_mapsTo p)
    (bridgeChartIncl_mapsTo (p.restrictTo U)) (totalInclOn_mapsTo p U)
    (fun z hz => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U z).mpr hz)
    (fun v hv => bridgeChartIncl_mapsTo p _ (totalInclOn_mapsTo p U v hv))
    (fun v hv => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U _).mpr
      (bridgeChartIncl_mapsTo (p.restrictTo U) v hv))

/-! ## 3. The bridge is natural in the base -/

set_option maxHeartbeats 1000000 in
/-- **The Thom bridge is natural in the base.**  `bridgeTotal_natural` with both
of its squares supplied, so a consumer restricting a class of the vector-bundle
pair to a compact Hausdorff part of the base can carry it across the bridge.

The base of the restriction must be compact Hausdorff, because `bridgeTotal`
itself is: the statement is unavailable over an arbitrary neighbourhood, and that
is why the fibre route restricts to a point. -/
theorem bridgeTotalRestrict [CompactSpace X] [T2Space X] (p : Bundle X ι)
    (U : Set X) [CompactSpace ↥U] [T2Space ↥U] (n : ℕ)
    (x : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    (relPullback (ZMod 2) (cmap (Bundle.projInclOn p.plusOne U))
        (fun z hz => projInclOn_range_mapsTo p U z hz) n).hom
        (ThomChernDeg.bridgeTotal p n x)
      = ThomChernDeg.bridgeTotal (p.restrictTo U) n
          ((relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U))
            (totalInclOn_mapsTo p U) n).hom x) :=
  bridgeTotal_natural p U n
    (relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U)) (totalInclOn_mapsTo p U) n)
    (relPullback (ZMod 2) (cmap (Bundle.projInclOn p.plusOne U))
      (fun z hz => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U z).mpr hz) n)
    (relPullback (ZMod 2) (cmap (Bundle.projInclOn p.plusOne U))
      (fun z hz => projInclOn_range_mapsTo p U z hz) n)
    (chartSquare p U n) (hyperSquare p U n) x

/-! Audited on every build: `#audit_axioms` prints the axiom closure and
**fails the build** if it leaves the classical allowlist, which `#print axioms`
does not. -/

#audit_axioms bridgeTotalRestrict

end

end GroupApproximation.CharClass
