import GroupApproximation.CharClass.ThomStepCOddIso

/-!
# `hinj` from a local restriction, which need only be injective

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomStepCOddIso.topChernClass_ne_zero_odd_iso` asks for an **isomorphism** `e`
together with `hcomp : sRel ≫ t = e.hom`.  Read carefully, `e` is used for one
thing only: injectivity of `sRel ≫ t`.  So the isomorphism is more than the proof
needs, and this file asks for less.

## What replaces `e` and `hcomp`

Two things, and each is a one-application target rather than a construction.

* `res` — the restriction of the pair to a trivialising neighbourhood of the
  section's zero, together with `hres`, that it is **injective**.
* `hsq` — that sectioning then charting agrees with restricting then trivialising.

**`hres` is not excision, and saying so was a mistake this docstring exists to
undo.**  Excision would need the part of the total space over the complement of
the neighbourhood to have its closure inside the punctured set; it does not,
because that part contains zero-section points, which are exactly what the
punctured set omits.  The Thom class does not localise to a ball: the relative
group of the full pair has rank the number of components of the base, and the
local one has rank one.  What is true is that under the Thom isomorphism on each
side `res` becomes restriction of degree-zero cohomology from the base to the
neighbourhood, and that is injective exactly when the base is **connected**.  For
the LIX base — a circle times a five-sphere times a product of complex projective
spaces — it is.

The identification `loc` of the restricted pair with the local model is already
unconditional: it is `cc-lix-odd`'s `lixLocalPairIsoClosed`.

## Why this is weaker than the isomorphism form, and not merely different

`topChernClass_ne_zero_odd_iso` can be recovered by taking `res := e.hom` and
`loc := Iso.refl`, so anything that discharges the iso form discharges this one.
The converse fails: an injective `res` that is not surjective is enough here and
is not enough there.  Stating it the other way round would have been the
over-ask this fleet has now met three times.

## Main declarations

* `injective_comp_of_square` — the algebra.
* `topChernClass_ne_zero_odd_local` — **Step C's odd side over `res`, `hsq`, `hres`.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **A composite that factors through an injective map and an isomorphism is
injective.**  Neither factor of the composite need be invertible. -/
theorem injective_comp_of_square {A B C D : ModuleCat.{0} (ZMod 2)}
    (f : A ⟶ B) (t : B ⟶ D) (res : A ⟶ C) (loc : C ≅ D)
    (hsq : f ≫ t = res ≫ loc.hom) (hres : Function.Injective res.hom) :
    Function.Injective (f ≫ t).hom := by
  intro x y hxy
  rw [hsq] at hxy
  have h1 : loc.hom.hom (res.hom x) = loc.hom.hom (res.hom y) := hxy
  have h2 := congrArg (fun w : D => loc.inv.hom w) h1
  simp only [iso_inv_hom_apply] at h2
  exact hres h2

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step C's odd side, with `hinj` given by a local restriction.**

`res` restricts the bundle pair to a trivialising neighbourhood of the section's
zero and `loc` identifies that with the local model; `hsq` says sectioning then
charting is restricting then trivialising.  Only **injectivity** of `res` is
used; see the header for why that is a connectedness statement about the base
and not an excision. -/
theorem topChernClass_ne_zero_odd_local (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart HrelE HE W HlocE : ModuleCat.{0} (ZMod 2)} {r : ℕ}
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
    (t : rel ⟶ W) (res : HrelE ⟶ HlocE) (loc : HlocE ≅ W)
    (hsq : sRel ≫ t = res ≫ loc.hom) (hres : Function.Injective res.hom)
    {u : HrelE} (hu : u ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_odd hacyclic j i hexact absLine exc chartIso jE sRel sAbs
    piStar hnat hsection t (injective_comp_of_square sRel t res loc hsq hres) hu hclass

/-- **The isomorphism form is a special case**, so nothing that discharged it is
lost.  Take the restriction to be `e.hom` and the identification to be the
identity. -/
theorem topChernClass_ne_zero_odd_local_of_iso (hacyclic : PuncturedAcyclic N twoR z)
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
  topChernClass_ne_zero_odd_local hacyclic j i hexact absLine exc chartIso jE sRel
    sAbs piStar hnat hsection t e.hom (Iso.refl W) (by rw [hcomp]; simp)
    (fun x y hxy => by
      have h := congrArg (fun w : W => e.inv.hom w) hxy
      simpa [iso_inv_hom_apply] using h)
    hu hclass

/-! Printed on every build. -/

#print axioms topChernClass_ne_zero_odd_local

end

end GroupApproximation.CharClass
