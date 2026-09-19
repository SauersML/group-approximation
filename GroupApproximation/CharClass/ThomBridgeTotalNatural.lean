import GroupApproximation.CharClass.ThomBridgeChartHom
import GroupApproximation.CharClass.ThomBridgeTotal

/-!
# The bridge is natural in the base

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

The composite of the two squares.  `ThomBridgeChartHom.bridgeChart_natural` is the
first two steps and `ThomBridgeNaturalHyper.relPullback_id_comm` the third; joining
them has to cross the one **inverted** isomorphism in `bridgeTotal`'s definition,
which is `inv_natural_of_hom_natural` and is category algebra with no content.

## Why the restricted base must be compact Hausdorff

`bridgeTotal` needs `[CompactSpace X] [T2Space X]`, because its third step goes
through `cc-bundle`'s `projInclHomeoRange`, which is built from a **closed**
embedding.  So `bridgeTotal (p.restrictTo U)` does not exist for an arbitrary `U`,
and in particular **not for a ball**.

That is not a defect in the route, it is why the route restricts to a **point**.
A one-point subtype is compact and Hausdorff for free, so the naturality below
applies at the fibre over the section's zero, which is exactly where the fibre
route needs it.  Stating it with the instances on `↥U` rather than assuming an
arbitrary open makes that visible instead of discovering it at the use site.

## Main declarations

* `inv_natural_of_hom_natural` — a naturality square inverts.
* `bridgeTotal_natural` — **the bridge is natural in the base.**
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

open ThomChernDeg

noncomputable section

/-- **A naturality square inverts.**  Pure category algebra. -/
theorem inv_natural_of_hom_natural {A B C D : ModuleCat.{0} (ZMod 2)}
    (e : A ≅ B) (f : C ≅ D) (T : B ⟶ D) (P : A ⟶ C)
    (h : e.hom ≫ T = P ≫ f.hom) : T ≫ f.inv = e.inv ≫ P := by
  have h1 : e.inv ≫ (P ≫ f.hom) = T := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  calc T ≫ f.inv = (e.inv ≫ (P ≫ f.hom)) ≫ f.inv := by rw [h1]
    _ = e.inv ≫ P := by
        rw [Category.assoc, Category.assoc, f.hom_inv_id, Category.comp_id]

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Unfolding `bridgeTotal` at a point: the chart isomorphism inverted, then the
hyperplane step. -/
theorem bridgeTotal_apply [CompactSpace X] [T2Space X] (p : Bundle X ι) (n : ℕ)
    (x : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    bridgeTotal p n x
      = (relPullback (ZMod 2) (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
          (fun _ hx => range_projIncl_subset_notZero p hx) n).hom
            ((bridgeChart p n).inv.hom x) := rfl

/-- **The bridge is natural in the base.**

`hchart` is `ThomBridgeChartHom.bridgeChart_natural` and `hhyp` is
`ThomBridgeNaturalHyper.relPullback_id_comm`; both are landed, and they are
arguments here only so that the statement fits without repeating their six and
four map-of-pairs conditions.  The content is the join across the inverted
isomorphism, which is `inv_natural_of_hom_natural`. -/
theorem bridgeTotal_natural [CompactSpace X] [T2Space X] (p : Bundle X ι) (U : Set X)
    [CompactSpace ↥U] [T2Space ↥U] (n : ℕ)
    (T : relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n ⟶
      relCohomology (ZMod 2) (TopCat.of (Bundle.Total (p.restrictTo U)))
        ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
          Bundle.puncturedSet (p.restrictTo U)) n)
    (Pn : relCohomology (ZMod 2) (TopCat.of (Bundle.Proj p.plusOne))
        ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)) n ⟶
      relCohomology (ZMod 2) (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne))
        ((Gysin.notZeroOpens (p.restrictTo U) :
            Opens (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
          : Set (Bundle.Proj (p.restrictTo U).plusOne)) n)
    (Pr : relCohomology (ZMod 2) (TopCat.of (Bundle.Proj p.plusOne))
        (Set.range (Bundle.projIncl p)) n ⟶
      relCohomology (ZMod 2) (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne))
        (Set.range (Bundle.projIncl (p.restrictTo U))) n)
    (hchart : (bridgeChart p n).hom ≫ T = Pn ≫ (bridgeChart (p.restrictTo U) n).hom)
    (hhyp : (relPullback (ZMod 2) (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
          (fun _ hx => range_projIncl_subset_notZero p hx) n) ≫ Pr
        = Pn ≫ (relPullback (ZMod 2) (𝟙 (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
          (fun _ hx => range_projIncl_subset_notZero (p.restrictTo U) hx) n))
    (x : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    Pr.hom (bridgeTotal p n x)
      = bridgeTotal (p.restrictTo U) n (T.hom x) := by
  have hinv := inv_natural_of_hom_natural (bridgeChart p n)
    (bridgeChart (p.restrictTo U) n) T Pn hchart
  have hx : ((relPullback (ZMod 2) (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
        (fun _ hz => range_projIncl_subset_notZero p hz) n) ≫ Pr).hom
          ((bridgeChart p n).inv.hom x)
      = (Pn ≫ (relPullback (ZMod 2)
          (𝟙 (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)))
          (fun _ hz => range_projIncl_subset_notZero (p.restrictTo U) hz) n)).hom
          ((bridgeChart p n).inv.hom x) := by
    rw [hhyp]
    rfl
  have hy : (T ≫ (bridgeChart (p.restrictTo U) n).inv).hom x
      = ((bridgeChart p n).inv ≫ Pn).hom x := by
    rw [hinv]
  rw [bridgeTotal_apply, bridgeTotal_apply]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hx hy
  rw [hx, hy]
  rfl

/-! Printed on every build. -/

#print axioms bridgeTotal_natural

end

end GroupApproximation.CharClass
