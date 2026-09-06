import GroupApproximation.CharClass.EulerLocalAssembly
import GroupApproximation.CharClass.ThomEulerNaturality
import GroupApproximation.CharClass.RelativeLocalModel

/-!
# Step C with the local model and the naturality square discharged

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`EulerLocalAssembly.topChernClass_ne_zero_of_chain` states Step C over an abstract
local model, with `locEquiv`, `hg`, `hsu` and `hgamma` as four separate
hypotheses.  Three of the four are now discharged.

* `locEquiv` and `hg` come from `cc-relative`'s local model itself: taking
  `loc = H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂)` and `g = localGenerator r`, the equivalence is
  `localEquiv r` and the nonvanishing is `localGenerator_ne_zero r`.  Neither is
  an assumption any more.
* `hgamma` comes from `topClass_eq_of_naturality'`: the section is a map of
  pairs, and `π^*` splits `σ^*`, so `j^*(σ^* u) = γ_r` for the Thom class `u`.

What is left is **`hsu` alone**: the relative Euler class `σ^* u` excises to the
local generator.  That is hypothesis 6, `cc-projective`'s, and it is the only
open topological input on the odd side of Lemma 2 apart from the Thom class it
mentions.

## Main declarations

* `topChernClass_ne_zero_of_local` — `locEquiv` and `hg` gone.
* `topChernClass_ne_zero_of_local_naturality` — `hgamma` gone as well, so the odd
  side of Step C rests on `hsu` and the naturality data.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step C over `cc-relative`'s local model.**  `locEquiv` and `hg` are no
longer hypotheses: the local model is `H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂)`, its
one-dimensionality is `localEquiv r`, and the generator is nonzero by
`localGenerator_ne_zero r`. -/
theorem topChernClass_ne_zero_of_local (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absEquiv : cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2)
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hsu : (exc ≪≫ chartIso).hom.hom su = localGenerator r)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_chain hacyclic j i hexact absEquiv exc chartIso
    (localEquiv r) hsu (localGenerator_ne_zero r) hgamma

/-- **Step C with the naturality square discharged too.**  The relative Euler
class is `σ^* u` for the Thom class `u`, and `hgamma` is then
`topClass_eq_of_naturality'`.

**Do not read this as reducing the count to one.**  The square trades `hgamma`
for six arguments plus `hu : jE.hom u = piStar.hom gamma`, and `hu` is where the
Thom class enters, so it sits behind the same Leray–Hirsch ladder as everything
else.  What it buys is that `gamma` stops being an opaque parameter and is pinned
to the Thom class through the section.  Someone auditing what Step C owes should
count `hu` alongside `hsu`.  (`cc-lix-odd` caught this reading; the earlier
wording here said "only `hsu` remains open", which invites an undercount.) -/
theorem topChernClass_ne_zero_of_local_naturality (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart HrelE HE : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absEquiv : cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2)
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (piStar : cohomologyZMod2 (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (cohomologyZMod2 (TopCat.of N) twoR))
    {u : HrelE} {gamma : cohomologyZMod2 (TopCat.of N) twoR}
    (hu : jE.hom u = piStar.hom gamma)
    (hsu : (exc ≪≫ chartIso).hom.hom (sRel.hom u) = localGenerator r) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_local hacyclic j i hexact absEquiv exc chartIso hsu
    (topClass_eq_of_naturality' jE j sRel sAbs piStar hnat hsection hu).symm

/-! ## 2. The top line as a `Nonempty` -/

/-- `topChernClass_ne_zero_of_local` with the top line taken as a `Nonempty`.

The conclusion is a `Prop`, so the equivalence is only ever used to prove one and
`Nonempty.elim` suffices: a consumer holding a `HasTopLine`, whose `line` field is
a `Nonempty`, need not perform a `Nonempty.some` of its own.  Published under a
new name because `topChernClass_ne_zero_of_chain` is already consumed.

This is **hygiene, not foundations.**  It does not make anything choice-free:
the mod-2 cohomology development and the Mathlib beneath it use `Classical.choice`
throughout, and `#print axioms` reports it for every theorem here.  What it
removes is a gratuitous `Nonempty.some` in the *consumer's* own code, which is
the consumer's responsibility in a way that Mathlib's use is not.  `cc-lix-odd`
measured this rather than assuming it, and the narrow claim is one word away from
a wide false one. -/
theorem topChernClass_ne_zero_of_local_line (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hsu : (exc ≪≫ chartIso).hom.hom su = localGenerator r)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 := by
  obtain ⟨absEquiv⟩ := absLine
  exact topChernClass_ne_zero_of_local hacyclic j i hexact absEquiv exc chartIso hsu hgamma

/-- The same over an abstract local model, for a consumer that has not yet
instantiated `cc-relative`'s. -/
theorem topChernClass_ne_zero_of_chain_line (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart loc : ModuleCat.{0} (ZMod 2)}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : rel ≅ chart) (chartIso : chart ≅ loc) (locEquiv : loc ≃ₗ[ZMod 2] ZMod 2)
    {su : rel} {g : loc} (hsu : (exc ≪≫ chartIso).hom.hom su = g) (hg : g ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 := by
  obtain ⟨absEquiv⟩ := absLine
  exact topChernClass_ne_zero_of_chain hacyclic j i hexact absEquiv exc chartIso
    locEquiv hsu hg hgamma

/-! The axiom list, printed on every build so the narrow claim above cannot drift
into the wide one.  Both report `[propext, Classical.choice, Quot.sound]`. -/

#print axioms topChernClass_ne_zero_of_local
#print axioms topChernClass_ne_zero_of_local_line

end

end GroupApproximation.CharClass
