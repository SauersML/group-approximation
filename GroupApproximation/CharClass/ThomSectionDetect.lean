import GroupApproximation.CharClass.ThomStepCSection
import GroupApproximation.CharClass.ThomSphereSubspace

/-!
# Closing the section predicate

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 6).

`ThomStepCSection.lean` reduced Step C's odd side to `SectionDetectsThom`, that
the section pullback does not kill the Thom class.  This file closes it over the
sphere route, leaving one geometric statement named rather than assumed.

The reduction is in two moves.

* **The Thom class is nonzero for free.**  `ThomStepCSection.thomClass_ne_zero`
  gets it from the degreewise identification of the relative group with the top
  Leray–Hirsch coefficient group.  No topology.
* **So the predicate is exactly injectivity of one composite.**  If restriction
  to a trivialising chart, followed by the identification of that chart's
  relative group with the local model, is injective after the section, then a
  nonzero Thom class stays nonzero.  That composite is where the section's zero
  being nondegenerate enters, through `eulerLocalHomeo`, whose derivative is
  invertible: the section is then a homeomorphism of punctured pairs near its
  zero, and mod 2 a homeomorphism of pairs induces an isomorphism, with no degree
  computation.

What the sphere route supplies is the middle object.  Over a trivialising
neighbourhood the pair is a product pair (`ThomBundlePair.bundlePairTrivIso`), its
subspace is a product with a sphere after `cc-bundle`'s replacement, and then
`ThomSphereSubspace.relQuotEquiv_of_sphere` identifies the relative group with the
base's cohomology — with no Künneth of pairs and no hypothesis on the base.

## Main declarations

* `sectionDetectsThom_of_detect` — any map detecting the class suffices.
* `sectionDetectsThom_of_injective` — **the predicate is injectivity of the
  chart composite**, given the Thom class is nonzero.
* `topChernClass_ne_zero_of_chartInjective` — Step C over that injectivity.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Detecting the class -/

/-- **Any map that detects the relative Euler class closes the predicate.** -/
theorem sectionDetectsThom_of_detect {HrelE rel W : ModuleCat.{0} (ZMod 2)}
    (sRel : HrelE ⟶ rel) (t : rel ⟶ W) {u : HrelE}
    (h : t.hom (sRel.hom u) ≠ 0) : SectionDetectsThom sRel u :=
  ne_zero_of_map_ne_zero t h

/-- **The predicate is injectivity of the chart composite.**

`u ≠ 0` is free, so all that is left is that restricting to the chart and
identifying with the local model does not kill it.  That is the one place the
section's zero has to be nondegenerate, and it is a statement about the section
rather than about the Thom class. -/
theorem sectionDetectsThom_of_injective {HrelE rel W : ModuleCat.{0} (ZMod 2)}
    (sRel : HrelE ⟶ rel) (t : rel ⟶ W)
    (hinj : Function.Injective (sRel ≫ t).hom) {u : HrelE} (hu : u ≠ 0) :
    SectionDetectsThom sRel u := by
  refine sectionDetectsThom_of_detect sRel t ?_
  intro h
  refine hu (hinj ?_)
  rw [map_zero]
  rw [ModuleCat.comp_apply]
  exact h

/-! ## 2. Step C over the chart injectivity -/

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step C, with the odd side resting on one geometric statement.**  Every
other hypothesis is discharged in this lane or `cc-relative`'s; what remains is
that the chart composite is injective after the section, which is the
nondegeneracy of the section's zero. -/
theorem topChernClass_ne_zero_of_chartInjective (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart HrelE W : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (sRel : HrelE ⟶ rel) (t : rel ⟶ W)
    (hinj : Function.Injective (sRel ≫ t).hom) {u : HrelE} (hu : u ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom (sRel.hom u)) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_section hacyclic j i hexact absLine exc chartIso sRel
    (sectionDetectsThom_of_injective sRel t hinj hu) hgamma

/-! Printed on every build. -/

#print axioms topChernClass_ne_zero_of_chartInjective

end

end GroupApproximation.CharClass
