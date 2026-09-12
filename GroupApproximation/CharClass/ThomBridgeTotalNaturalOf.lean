import GroupApproximation.CharClass.ThomChartSquare
import GroupApproximation.CharClass.ThomBridgeTotalOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Thom bridge over a field is natural in the base

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomBridgeTotalNatural` and `ThomChartSquare` show at `F₂` that the Thom bridge commutes with
restricting the base to a compact Hausdorff part `U`.  The argument joins two squares across
the inverted chart isomorphism: the chart square (`bridgeChart_natural`) and the hyperplane
square (`hyperSquare`, already over any ring).  Over a field `K` the chart square is
`bridgeChartOf_natural`, and the join is category algebra over any ring.

## Main declarations

* `inv_natural_of_hom_naturalOf` — a naturality square inverts, over any ring.
* `bridgeTotalOf_natural` — the join.
* `chartSquareOf` — the chart square at the bundle's own objects.
* `bridgeTotalRestrictOf` — **the Thom bridge over a field is natural in the base**.
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace GroupApproximation.CharClass

noncomputable section

open ThomChernDeg

/-- **A naturality square inverts**, over any ring. -/
theorem inv_natural_of_hom_naturalOf {R : Type} [Ring R] {A B C D : ModuleCat.{0} R}
    (e : A ≅ B) (f : C ≅ D) (T : B ⟶ D) (P : A ⟶ C)
    (h : e.hom ≫ T = P ≫ f.hom) : T ≫ f.inv = e.inv ≫ P := by
  have h1 : e.inv ≫ (P ≫ f.hom) = T := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  calc T ≫ f.inv = (e.inv ≫ (P ≫ f.hom)) ≫ f.inv := by rw [h1]
    _ = e.inv ≫ P := by
        rw [Category.assoc, Category.assoc, f.hom_inv_id, Category.comp_id]

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Unfolding `bridgeTotalOf` at a point. -/
theorem bridgeTotalOf_apply (K : Type) [Field K] [CompactSpace X] [T2Space X] (p : Bundle X ι)
    (n : ℕ)
    (x : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    bridgeTotalOf K p n x
      = (relPullback K (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
          (fun _ hx => range_projIncl_subset_notZero p hx) n).hom
            ((bridgeChartOf K p n).inv.hom x) := rfl

/-- **The bridge over a field is natural in the base**, given the chart square and the
hyperplane square. -/
theorem bridgeTotalOf_natural (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) (U : Set X) [CompactSpace ↥U] [T2Space ↥U] (n : ℕ)
    (T : relCohomology K (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n ⟶
      relCohomology K (TopCat.of (Bundle.Total (p.restrictTo U)))
        ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
          Bundle.puncturedSet (p.restrictTo U)) n)
    (Pn : relCohomology K (TopCat.of (Bundle.Proj p.plusOne))
        ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)) n ⟶
      relCohomology K (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne))
        ((Gysin.notZeroOpens (p.restrictTo U) :
            Opens (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
          : Set (Bundle.Proj (p.restrictTo U).plusOne)) n)
    (Pr : relCohomology K (TopCat.of (Bundle.Proj p.plusOne))
        (Set.range (Bundle.projIncl p)) n ⟶
      relCohomology K (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne))
        (Set.range (Bundle.projIncl (p.restrictTo U))) n)
    (hchart : (bridgeChartOf K p n).hom ≫ T = Pn ≫ (bridgeChartOf K (p.restrictTo U) n).hom)
    (hhyp : (relPullback K (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
          (fun _ hx => range_projIncl_subset_notZero p hx) n) ≫ Pr
        = Pn ≫ (relPullback K (𝟙 (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
          (fun _ hx => range_projIncl_subset_notZero (p.restrictTo U) hx) n))
    (x : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    Pr.hom (bridgeTotalOf K p n x)
      = bridgeTotalOf K (p.restrictTo U) n (T.hom x) := by
  have hinv := inv_natural_of_hom_naturalOf (bridgeChartOf K p n)
    (bridgeChartOf K (p.restrictTo U) n) T Pn hchart
  have hx : ((relPullback K (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
        (fun _ hz => range_projIncl_subset_notZero p hz) n) ≫ Pr).hom
          ((bridgeChartOf K p n).inv.hom x)
      = (Pn ≫ (relPullback K
          (𝟙 (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
          (fun _ hz => range_projIncl_subset_notZero (p.restrictTo U) hz) n)).hom
          ((bridgeChartOf K p n).inv.hom x) := by
    rw [hhyp]
    rfl
  have hy : (T ≫ (bridgeChartOf K (p.restrictTo U) n).inv).hom x
      = ((bridgeChartOf K p n).inv ≫ Pn).hom x := by
    rw [hinv]
  rw [bridgeTotalOf_apply, bridgeTotalOf_apply]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hx hy
  rw [hx, hy]
  rfl

/-- **The first two bridge steps over a field are natural in the base, at the bundle's own
objects.** -/
theorem chartSquareOf (K : Type) [Field K] (p : Bundle X ι) (U : Set X) (n : ℕ) :
    (bridgeChartOf K p n).hom
        ≫ relPullback K (cmap (Bundle.totalInclOn p U))
            (totalInclOn_mapsTo p U) n
      = relPullback K (cmap (Bundle.projInclOn p.plusOne U))
          (fun z hz => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U z).mpr hz) n
        ≫ (bridgeChartOf K (p.restrictTo U) n).hom :=
  bridgeChartOf_natural K p U n (bridgeChartIncl_mapsTo p)
    (bridgeChartIncl_mapsTo (p.restrictTo U)) (totalInclOn_mapsTo p U)
    (fun z hz => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U z).mpr hz)
    (fun v hv => bridgeChartIncl_mapsTo p _ (totalInclOn_mapsTo p U v hv))
    (fun v hv => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U _).mpr
      (bridgeChartIncl_mapsTo (p.restrictTo U) v hv))

set_option maxHeartbeats 1000000 in
/-- **The Thom bridge over a field is natural in the base.** -/
theorem bridgeTotalRestrictOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) (U : Set X) [CompactSpace ↥U] [T2Space ↥U] (n : ℕ)
    (x : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    (relPullback K (cmap (Bundle.projInclOn p.plusOne U))
        (fun z hz => projInclOn_range_mapsTo p U z hz) n).hom
        (bridgeTotalOf K p n x)
      = bridgeTotalOf K (p.restrictTo U) n
          ((relPullback K (cmap (Bundle.totalInclOn p U))
            (totalInclOn_mapsTo p U) n).hom x) :=
  bridgeTotalOf_natural K p U n
    (relPullback K (cmap (Bundle.totalInclOn p U)) (totalInclOn_mapsTo p U) n)
    (relPullback K (cmap (Bundle.projInclOn p.plusOne U))
      (fun z hz => (Bundle.projInclOn_mem_notZeroOpensSet_iff p U z).mpr hz) n)
    (relPullback K (cmap (Bundle.projInclOn p.plusOne U))
      (fun z hz => projInclOn_range_mapsTo p U z hz) n)
    (chartSquareOf K p U n) (hyperSquare K p U n) x

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms bridgeTotalRestrictOf

end

end GroupApproximation.CharClass
