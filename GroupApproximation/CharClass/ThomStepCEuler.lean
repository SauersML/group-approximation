import GroupApproximation.CharClass.ThomStepCLocal
import GroupApproximation.CharClass.MayerVietorisElement

/-!
# `hsu` is exactly the nonvanishing of the relative Euler class

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 6).

`ThomStepCLocal.lean` left one open hypothesis on the odd side,

```text
hsu : (exc ≪≫ chartIso).hom.hom su = localGenerator r,
```

that the relative Euler class `σ^* u` excises to the generator of
`H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂)`.  Stated that way it looks like an identification of
two specific classes, which is how the manuscript phrases it.  It is not: the
local model is **one dimensional**, and `exc ≪≫ chartIso` is an **isomorphism**,
so a class either maps to zero or maps to the only nonzero element there.  Hence

```text
hsu   ⟺   su ≠ 0,
```

and the equality half is free.  That is the content of this file.

This does not make hypothesis 6 disappear — `su ≠ 0` is still the local
statement, and it still needs the section's zero to be nondegenerate, which is
what `eulerLocalHomeo` supplies.  What it does is remove the *identification*
from the interface, leaving a nonvanishing.  A nonvanishing is the shape the rest
of Step C already speaks, since `topChernClass_ne_zero` propagates `su ≠ 0` to
`γ_r ≠ 0` through the punctured acyclicity.

## Main declarations

* `eq_localGenerator_of_ne_zero` — one dimensionality, in usable form.
* `hsu_of_ne_zero` — **the reduction**: `su ≠ 0` gives `hsu`.
* `topChernClass_ne_zero_of_su_ne_zero`, `..._line` — Step C with `hsu` replaced
  by the nonvanishing of the relative Euler class.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-! ## 1. The local model has one nonzero element -/

/-- **The local model is a line, so its only nonzero element is the generator.** -/
theorem eq_localGenerator_of_ne_zero (r : ℕ)
    {a : relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r)}
    (ha : a ≠ 0) : a = localGenerator r := by
  have hone : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have h0 : localEquiv r a ≠ 0 := by
    intro h0
    exact ha (by rw [eq_smul_localGenerator r a, h0, zero_smul])
  calc a = (localEquiv r a) • localGenerator r := eq_smul_localGenerator r a
    _ = (1 : ZMod 2) • localGenerator r := by rw [hone _ h0]
    _ = localGenerator r := one_smul _ _

/-! ## 2. The reduction -/

/-- **`hsu` is exactly `su ≠ 0`.**  The excision and chart isomorphisms compose to
an isomorphism onto a one-dimensional space, so a nonzero class has nowhere to go
but the generator. -/
theorem hsu_of_ne_zero {rel chart : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hne : su ≠ 0) :
    (exc ≪≫ chartIso).hom.hom su = localGenerator r := by
  refine eq_localGenerator_of_ne_zero r ?_
  intro h
  exact hne (eq_zero_of_iso_hom_eq_zero (exc ≪≫ chartIso) h)

/-- The converse, so that the two forms are interchangeable at the interface. -/
theorem ne_zero_of_hsu {rel chart : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hsu : (exc ≪≫ chartIso).hom.hom su = localGenerator r) :
    su ≠ 0 := by
  intro h
  rw [h, map_zero] at hsu
  exact localGenerator_ne_zero r hsu.symm

/-! ## 3. Step C over the nonvanishing -/

/-- **Step C with `hsu` replaced by the nonvanishing of the relative Euler class.**
Every hypothesis except that nonvanishing is now discharged inside this lane or
`cc-relative`'s. -/
theorem topChernClass_ne_zero_of_su_ne_zero (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absEquiv : cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2)
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hne : su ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_local hacyclic j i hexact absEquiv exc chartIso
    (hsu_of_ne_zero exc chartIso hne) hgamma

/-- The same with the top line as a `Nonempty`, so a consumer holding a
`HasTopLine` need not perform a `Nonempty.some` of its own.

This is **hygiene, not foundations.**  It does not make anything choice-free:
the mod-2 cohomology development and the Mathlib beneath it use `Classical.choice`
throughout, and `#print axioms` reports it for every theorem here.  What it
removes is a gratuitous `Nonempty.some` in the *consumer's* own code, which is
the consumer's responsibility in a way that Mathlib's use is not.  `cc-lix-odd`
measured this rather than assuming it, and the narrow claim is one word away from
a wide false one. -/
theorem topChernClass_ne_zero_of_su_ne_zero_line (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hne : su ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 := by
  obtain ⟨absEquiv⟩ := absLine
  exact topChernClass_ne_zero_of_su_ne_zero hacyclic j i hexact absEquiv exc chartIso
    hne hgamma

/-! ## 4. All three improvements in one statement -/

/-- **The combination.**  The nonvanishing form of `hsu`, the top line as a
`Nonempty`, and the naturality square, in a single theorem.

`cc-lix-odd` pointed out that the three improvements lived in three theorems and
that no one of them carried all three, so a consumer had to give up one.  This is
the one to restate against.

Read the reduction honestly: the naturality square does **not** remove
`hgamma`'s content.  It trades one hypothesis for six arguments plus `hu`, and
`hu : jE.hom u = piStar.hom gamma` is where the Thom class enters, so it is
behind the same Leray–Hirsch ladder as everything else.  What it buys is that
`gamma` is no longer an opaque parameter: it is pinned to the Thom class `u`
through the section.  A reader auditing what Step C owes should count `hu` and
`hne`, not `hne` alone. -/
theorem topChernClass_ne_zero_of_su_ne_zero_naturality_line
    (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart HrelE HE : ModuleCat.{0} (ZMod 2)} {r : ℕ}
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
    {u : HrelE} {gamma : cohomologyZMod2 (TopCat.of N) twoR}
    (hu : jE.hom u = piStar.hom gamma)
    (hne : sRel.hom u ≠ 0) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_su_ne_zero_line hacyclic j i hexact absLine exc chartIso hne
    (topClass_eq_of_naturality' jE j sRel sAbs piStar hnat hsection hu).symm

/-! Printed on every build, for the same reason. -/

#print axioms topChernClass_ne_zero_of_su_ne_zero_naturality_line

#print axioms topChernClass_ne_zero_of_su_ne_zero
#print axioms topChernClass_ne_zero_of_su_ne_zero_line

end

end GroupApproximation.CharClass
