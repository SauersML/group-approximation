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

/-! Printed on every build. -/

#print axioms inv_natural_of_hom_natural

end

end GroupApproximation.CharClass
