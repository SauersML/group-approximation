import GroupApproximation.CharClass.ThomSectionDetect

/-!
# Step C's odd side over one field

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomSectionDetect.topChernClass_ne_zero_of_chartInjective` takes the chart
injectivity but still carries `hgamma`, the identification of the top Chern class
with the image of the Thom class.  `ThomStepCEuler`'s naturality variant
discharges `hgamma` but does not take the chart injectivity.  So the two
improvements lived in two theorems and a consumer had to give one up.  This file
takes both, which is what `cc-lix-odd` needs to restate `ThomChainOpen` down to a
single field.

## A caution about what `hinj` is, and is not

`hinj` is injectivity of `sRel ≫ t`.  Injectivity of a composite implies
injectivity of its first factor, so `hinj` is **never weaker** than injectivity
of the section map alone, whatever middle object `t` is; and if `t` is taken to
be an isomorphism — the excision-and-chart isomorphism being the obvious
candidate — then `hinj` is *exactly* injectivity of `sRel` and the chart has
bought nothing.

So the content cannot come from the chart.  It has to come from the section being
a homeomorphism of punctured pairs near its zero, which is
`cc-lix-odd`'s `lixChartPairHomeo` and `lixLocalRelIso`.  The observation is
theirs; it is recorded here because this is the signature someone will
instantiate, and the natural instinct is to plug in the chart isomorphism and
feel that something has been gained.

## Main declaration

* `topChernClass_ne_zero_odd` — Step C's odd side, over `hinj` and the
  naturality square, with `hgamma` discharged.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step C's odd side, with both improvements at once.**  The chart injectivity
and the naturality square together, so `hgamma` is no longer a hypothesis: it is
`topClass_eq_of_naturality'` applied to the section as a map of pairs. -/
theorem topChernClass_ne_zero_odd (hacyclic : PuncturedAcyclic N twoR z)
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
    (t : rel ⟶ W) (hinj : Function.Injective (sRel ≫ t).hom)
    {u : HrelE} (hu : u ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_chartInjective hacyclic j i hexact absLine exc chartIso
    sRel t hinj hu
    (topClass_eq_of_naturality' jE j sRel sAbs piStar hnat hsection hclass).symm

/-! Printed on every build. -/

#print axioms topChernClass_ne_zero_odd

end

end GroupApproximation.CharClass
