import GroupApproximation.CharClass.ThomStepCEulerOf
import GroupApproximation.CharClass.RelativeLocalModelOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Step C over a field, against the local model `H^{2r}(ℂ^r, ℂ^r ∖ 0; K)`

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomStepCEulerOf` states Step C over a field with the local model an abstract line.  This
file instantiates it at `lix-coeff`'s local model over `K`, whose one-dimensionality is
`localEquivOf K r`, so the `modelLine` hypothesis disappears.

It also records the correct `K`-form of the `F₂` lemma `hsu_of_ne_zero`.  Over `F₂` a
nonzero relative Euler class excises to *the* generator; over a field it excises to a
**unit multiple** of the generator (`hsu_isUnit_of_ne_zeroOf`).  No consumer of Step C needs
the unit: the theorems below conclude `γ_r ≠ 0` from `su ≠ 0` directly.

## Main declarations

* `hsu_isUnit_of_ne_zeroOf` — a nonzero relative Euler class excises to a unit multiple of
  `localGeneratorOf K r`.
* `topChernClass_ne_zero_of_localOf` — Step C over a field at the local model, with the
  naturality square.
* `topChernClass_ne_zero_odd_localModelOf` — the odd side over a field at the local model,
  with the section's nondegeneracy as a local restriction.
-/

set_option autoImplicit false

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

/-- **The `K`-form of `hsu_of_ne_zero`.**  A nonzero class excises to a unit multiple of the
generator of the local model. -/
theorem hsu_isUnit_of_ne_zeroOf {K : Type} [Field K] {rel chart : ModuleCat.{0} K} {r : ℕ}
    (exc : rel ≅ chart)
    (chartIso : chart ≅ relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hne : su ≠ 0) :
    IsUnit (localEquivOf K r ((exc ≪≫ chartIso).hom.hom su)) ∧
      (exc ≪≫ chartIso).hom.hom su
        = localEquivOf K r ((exc ≪≫ chartIso).hom.hom su) • localGeneratorOf K r :=
  ⟨isUnit_localEquivOf_of_ne_zero K r (iso_hom_ne_zeroOf (exc ≪≫ chartIso) hne),
    eq_smul_localGeneratorOf K r _⟩

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step C over a field at the local model.**  The nonvanishing of the relative Euler class
together with the naturality square gives `γ_r ≠ 0`. -/
theorem topChernClass_ne_zero_of_localOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z) {rel chart HrelE HE : ModuleCat.{0} K} {r : ℕ}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart)
    (chartIso : chart ≅ relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    {u : HrelE} {gamma : Hmod K (TopCat.of N) twoR}
    (hu : jE.hom u = piStar.hom gamma) (hne : sRel.hom u ≠ 0) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_su_ne_zero_naturalityOf hacyclic j i hexact absLine exc chartIso
    ⟨localEquivOf K r⟩ jE sRel sAbs piStar hnat hsection hu hne

/-- **The odd side over a field at the local model**, with the section's nondegeneracy given
by a local restriction `res` and a trivialisation `trivIso`. -/
theorem topChernClass_ne_zero_odd_localModelOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z)
    {rel chart HrelE HE W HlocE : ModuleCat.{0} K} {r : ℕ}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart)
    (chartIso : chart ≅ relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    (t : rel ⟶ W) (res : HrelE ⟶ HlocE) (trivIso : HlocE ≅ W)
    (hsq : sRel ≫ t = res ≫ trivIso.hom) (hres : Function.Injective res.hom)
    {u : HrelE} (hu : u ≠ 0) {gamma : Hmod K (TopCat.of N) twoR}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_odd_localOf hacyclic j i hexact absLine exc chartIso
    ⟨localEquivOf K r⟩ jE sRel sAbs piStar hnat hsection t res trivIso hsq hres hu hclass

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms hsu_isUnit_of_ne_zeroOf
#audit_axioms topChernClass_ne_zero_of_localOf
#audit_axioms topChernClass_ne_zero_odd_localModelOf

end

end GroupApproximation.CharClass
