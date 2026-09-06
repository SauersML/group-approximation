import GroupApproximation.CharClass.ThomBridgeChart
import GroupApproximation.CharClass.ThomBridgeNaturalSquare
import GroupApproximation.CharClass.CohomologyBridge

/-!
# The first two bridge steps are a single relative pullback

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`bridgeChart` is built as excision followed by a congruence, but neither is
opaque: excision's forward map is a `relPullback` along an inclusion, and the
congruence is `relPairIso`, whose `hom` field **is** a `relPullback`.  So the two
steps compose, by `relPullback_comp`, into a single `relPullback` along one
continuous map, and that map is `bridgeChartIncl`.

This is what makes the naturality of the pair one square rather than two.  It is
`cc-lix-odd`'s observation that excision is not opaque, applied a layer up from
where they made it.

## Main declarations

* `bridgeChartIncl_map_eq` — the two space maps compose to `bridgeChartIncl`.
* `bridgeChart_hom_eq` — **the two steps are one pullback.**
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The excision inclusion after the chart identification **is** the chart
inclusion.  Pointwise `rfl`; stated as a morphism equality so that
`relPullback_eq_of_eq` can consume it. -/
theorem bridgeChartIncl_map_eq (p : Bundle X ι) :
    (TopCat.isoOfHomeo (Bundle.chartOpensHomeoTotal p).symm).hom
        ≫ sInclusion ((Gysin.chartOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne))
      = cmap (bridgeChartIncl p) := by
  apply TopCat.Hom.ext
  exact ContinuousMap.ext fun _ => rfl

/-- **The first two bridge steps are a single relative pullback**, along the chart
inclusion. -/
theorem bridgeChart_hom_eq (p : Bundle X ι) (n : ℕ)
    (h : ∀ v ∈ ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p),
      (ConcreteCategory.hom (cmap (bridgeChartIncl p))) v
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne))) :
    (bridgeChart p n).hom = relPullback (ZMod 2) (cmap (bridgeChartIncl p)) h n := by
  show relPullback (ZMod 2) _ _ n ≫ relPullback (ZMod 2) _ _ n = _
  rw [← relPullback_comp (ZMod 2) _ _ _ _
    (by
      intro v hv
      have := bridgeChartIncl_map_eq p
      exact (congrArg (fun g => (ConcreteCategory.hom g) v) this) ▸ h v hv) n]
  exact relPullback_eq_of_eq (ZMod 2) (bridgeChartIncl_map_eq p) _ n

/-! ## The square for the first two steps -/

/-- **The first two bridge steps are natural in the base.**  One application of
`relPullback_comm_of_map_eq` on top of `bridgeChartIncl_natural`, now that both
steps are a single pullback.  The six map-of-pairs conditions are arguments; at
the bridge they are `cc-bundle`'s two membership equivalences and the two
composites. -/
theorem bridgeChart_natural (p : Bundle X ι) (U : Set X) (n : ℕ)
    (ha : ∀ v ∈ ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p),
      (ConcreteCategory.hom (cmap (bridgeChartIncl p))) v
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)))
    (hd : ∀ v ∈ ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet (p.restrictTo U)),
      (ConcreteCategory.hom (cmap (bridgeChartIncl (p.restrictTo U)))) v
        ∈ ((Gysin.notZeroOpens (p.restrictTo U) :
            Opens (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
          : Set (Bundle.Proj (p.restrictTo U).plusOne)))
    (hb : ∀ v ∈ ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet (p.restrictTo U)),
      (ConcreteCategory.hom (cmap (Bundle.totalInclOn p U))) v
        ∈ ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p))
    (hc : ∀ z ∈ ((Gysin.notZeroOpens (p.restrictTo U) :
          Opens (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
        : Set (Bundle.Proj (p.restrictTo U).plusOne)),
      (ConcreteCategory.hom (cmap (Bundle.projInclOn p.plusOne U))) z
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)))
    (hba : ∀ v ∈ ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet (p.restrictTo U)),
      (ConcreteCategory.hom (cmap (Bundle.totalInclOn p U) ≫ cmap (bridgeChartIncl p))) v
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)))
    (hdc : ∀ v ∈ ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet (p.restrictTo U)),
      (ConcreteCategory.hom
        (cmap (bridgeChartIncl (p.restrictTo U)) ≫ cmap (Bundle.projInclOn p.plusOne U))) v
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne))) :
    (bridgeChart p n).hom ≫ relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U)) hb n
      = relPullback (ZMod 2) (cmap (Bundle.projInclOn p.plusOne U)) hc n
        ≫ (bridgeChart (p.restrictTo U) n).hom := by
  rw [bridgeChart_hom_eq p n ha, bridgeChart_hom_eq (p.restrictTo U) n hd]
  refine relPullback_comm_of_map_eq _ _ _ _ ?_ ha hb hc hd hba hdc n
  apply TopCat.Hom.ext
  exact ContinuousMap.ext fun v => bridgeChartIncl_natural p U v

/-! Printed on every build. -/

#print axioms bridgeChart_natural

end

end GroupApproximation.CharClass
