import GroupApproximation.CharClass.ThomStepCOdd

/-!
# Discharging `hinj` from an isomorphism, in one application

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomStepCOdd.topChernClass_ne_zero_odd` leaves `hinj`, injectivity of
`sRel ≫ t`, as the single open input.  This file shapes that input so that
`cc-lix-odd`'s `lixLocalRelIso` discharges it by **one application**.

## Why the composite, and not `t`

`cc-lix-odd`'s caution, and it decides the shape.  Injectivity of a composite
implies injectivity of its first factor, so `hinj` is never weaker than
injectivity of `sRel` alone; if `t` were taken to be an isomorphism, `hinj` would
be exactly that and the chart would contribute nothing.

The resolution is that it is the **composite** that is an isomorphism, not
either factor.  The section is a homeomorphism of punctured pairs near its zero,
so restricting to the chart and following the section is invertible even though
neither restricting nor sectioning is.  `injective_of_hom_eq_iso` takes exactly
that: an isomorphism together with the equation identifying the composite with
it.  So `t` remains the chart restriction, which is not injective in general, and
the content sits where it belongs.

## Main declarations

* `injective_of_hom_eq_iso` — a morphism equal to an isomorphism is injective.
* `topChernClass_ne_zero_odd_iso` — **Step C's odd side with `hinj` replaced by
  an isomorphism and one equation.**
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- A morphism that **equals** an isomorphism is injective.  Neither factor of a
composite need be invertible for the composite to be. -/
theorem injective_of_hom_eq_iso {A B : ModuleCat.{0} (ZMod 2)} (f : A ⟶ B)
    (e : A ≅ B) (h : f = e.hom) : Function.Injective f.hom := by
  intro x y hxy
  rw [h] at hxy
  have h1 := congrArg (fun w : B => e.inv.hom w) hxy
  simpa [iso_inv_hom_apply] using h1

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step C's odd side, with `hinj` given by an isomorphism.**  Supply the
isomorphism `e` witnessing that the section followed by the chart restriction is
invertible near the zero — `cc-lix-odd`'s `lixLocalRelIso` — together with the
equation identifying the composite with it, and the odd side closes. -/
theorem topChernClass_ne_zero_odd_iso (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart HrelE HE W : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel)
    (sAbs : HE ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (piStar : cohomologyZMod2 (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (cohomologyZMod2 (TopCat.of N) twoR))
    (t : rel ⟶ W) (e : HrelE ≅ W) (hcomp : sRel ≫ t = e.hom)
    {u : HrelE} (hu : u ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_odd hacyclic j i hexact absLine exc chartIso jE sRel sAbs
    piStar hnat hsection t (injective_of_hom_eq_iso (sRel ≫ t) e hcomp) hu hclass

/-! Printed on every build. -/

#print axioms topChernClass_ne_zero_odd_iso

end

end GroupApproximation.CharClass
