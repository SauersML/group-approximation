import GroupApproximation.CharClass.EulerLocalNonvanishing
import GroupApproximation.CharClass.ThomEulerNaturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Step C over a field: `γ_r ≠ 0` from the nonvanishing of the relative Euler class

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

Over `F₂`, `ThomStepCEuler.lean` proves Step C in two moves:

* a nonzero class of the local model *is* the generator (`eq_localGenerator_of_ne_zero`,
  by `decide` over `ZMod 2`), so `hsu` follows from `su ≠ 0`;
* `EulerLocalAssembly.topChernClass_ne_zero_of_chain` propagates the generator to
  `γ_r ≠ 0`.

The first move is false over every other field: a nonzero element of a line over `K` is
a unit multiple of a generator, not the generator.  It is also not needed.  Step C
concludes a nonvanishing, and the chain only uses the generator to know that `su ≠ 0`.
So over a field `K` the identification is dropped and the nonvanishing is the interface:

1. `j^* : H^{2r}(N, N ∖ z; K) → H^{2r}(N; K)` is surjective, because the punctured space
   has no `K`-cohomology in the top degree (`PuncturedAcyclicOf K`) and the long exact
   sequence of the pair is exact at `H^{2r}(N; K)`;
2. both groups are lines over `K`: the relative one through the excision and chart
   isomorphisms onto the local model, the absolute one by hypothesis;
3. a surjection between two lines over a field is injective
   (`ThomFieldTwo.injective_of_surjective_of_line`, no finiteness), so `su ≠ 0` gives
   `γ_r = j^*(su) ≠ 0`.

No generator is named and no unit is carried.  The `F₂` files are unchanged; the mod-`p`
Step C restates against the forms below.  The module algebra of §1 is over any ring and is
proved here rather than imported, so that this file's import closure stays two modules
wide.

## Main declarations

* `iso_hom_ne_zeroOf`, `injective_of_hom_eq_isoOf`, `injective_of_comp_injectiveOf`,
  `ne_zero_of_injective_compOf`, `injective_comp_of_squareOf` — the module algebra, over
  any ring.  `iso_hom_ne_zeroOf` replaces `hsu_of_ne_zero`, whose generator identification
  is special to `F₂`.
* `surjective_of_punctured_acyclicOf` — step 1, over any commutative ring.
* `topChernClass_ne_zero_of_chainOf` — steps 1–3 over a field.
* `topChernClass_ne_zero_of_su_ne_zero_naturalityOf` — the same with `γ_r` pinned to the
  Thom class through the section.
* `topChernClass_ne_zero_oddOf`, `topChernClass_ne_zero_odd_isoOf`,
  `topChernClass_ne_zero_odd_localOf` — the odd side over a field, with the section's
  nondegeneracy given as injectivity of the chart composite: directly, by an isomorphism, or
  by a local restriction.  These are the `K`-forms of the `F₂` theorems consumed by
  `LIXKStepC`, `LIXThomDatum`/`LIXStepCOddNamed` and `LIXStepCOddLocal`.
-/

set_option autoImplicit false

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Module algebra, over any ring -/

section Algebra

variable {R : Type} [Ring R]

/-- **The replacement for `hsu_of_ne_zero`.**  Over `F₂` a nonzero class of the local model
is the generator.  Over a field it is only a unit multiple of one, and no consumer needs
more than that it is nonzero, which any isomorphism preserves. -/
theorem iso_hom_ne_zeroOf {M M' : ModuleCat.{0} R} (e : M ≅ M') {x : M} (hx : x ≠ 0) :
    e.hom.hom x ≠ 0 := by
  intro h
  refine hx ?_
  have h1 : e.inv.hom (e.hom.hom x) = e.inv.hom 0 := by rw [h]
  rwa [hom_apply_of_comp_eq_id e.hom_inv_id x, map_zero] at h1

/-- A morphism that **equals** an isomorphism is injective. -/
theorem injective_of_hom_eq_isoOf {A B : ModuleCat.{0} R} (f : A ⟶ B) (e : A ≅ B)
    (h : f = e.hom) : Function.Injective f.hom := by
  subst h
  intro x y hxy
  have h1 : e.inv.hom (e.hom.hom x) = e.inv.hom (e.hom.hom y) := by rw [hxy]
  rwa [hom_apply_of_comp_eq_id e.hom_inv_id x, hom_apply_of_comp_eq_id e.hom_inv_id y] at h1

/-- Injectivity of a composite passes to its first factor. -/
theorem injective_of_comp_injectiveOf {A B D : ModuleCat.{0} R} (sRel : A ⟶ B) (t : B ⟶ D)
    (hinj : Function.Injective (sRel ≫ t).hom) : Function.Injective sRel.hom := by
  intro x y hxy
  refine hinj ?_
  show t.hom (sRel.hom x) = t.hom (sRel.hom y)
  rw [hxy]

/-- The image of a nonzero class under the first factor of an injective composite is
nonzero. -/
theorem ne_zero_of_injective_compOf {A B D : ModuleCat.{0} R} (sRel : A ⟶ B) (t : B ⟶ D)
    (hinj : Function.Injective (sRel ≫ t).hom) {u : A} (hu : u ≠ 0) : sRel.hom u ≠ 0 := by
  intro h0
  refine hu (injective_of_comp_injectiveOf sRel t hinj ?_)
  rw [h0, map_zero]

/-- A composite that factors as an injective map followed by an isomorphism is injective;
neither factor of the original composite need be invertible. -/
theorem injective_comp_of_squareOf {A B C D : ModuleCat.{0} R}
    (f : A ⟶ B) (t : B ⟶ D) (res : A ⟶ C) (trivIso : C ≅ D)
    (hsq : f ≫ t = res ≫ trivIso.hom) (hres : Function.Injective res.hom) :
    Function.Injective (f ≫ t).hom := by
  intro x y hxy
  rw [hsq] at hxy
  have h1 : trivIso.hom.hom (res.hom x) = trivIso.hom.hom (res.hom y) := hxy
  have h2 : trivIso.inv.hom (trivIso.hom.hom (res.hom x))
      = trivIso.inv.hom (trivIso.hom.hom (res.hom y)) := by rw [h1]
  rw [hom_apply_of_comp_eq_id trivIso.hom_inv_id,
    hom_apply_of_comp_eq_id trivIso.hom_inv_id] at h2
  exact hres h2

end Algebra

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-! ## 2. Surjectivity of `j^*`, over any commutative ring -/

/-- **Step 1 over `K`.**  The punctured space has no `K`-cohomology in the top degree, so
exactness of the pair sequence at `H^{twoR}(N; K)` makes `j^*` surjective. -/
theorem surjective_of_punctured_acyclicOf {K : Type} [CommRing K]
    (hacyclic : PuncturedAcyclicOf K N twoR z) {rel : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom) :
    Function.Surjective j.hom := by
  haveI := hacyclic.subsingleton_punctured_top
  exact ModuleCat.hom_surjective_of_exact_of_subsingleton j i hexact

/-! ## 3. Step C over a field -/

/-- **Step C over a field `K`, over an abstract local model.**  A nonzero class `su` of
the relative group stays nonzero under `j^*`, once the relative group is a line
(transported from the local model along `exc ≪≫ chartIso`) and the absolute group is a
line. -/
theorem topChernClass_ne_zero_of_chainOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z) {rel chart model : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart) (chartIso : chart ≅ model) (modelLine : Nonempty (model ≃ₗ[K] K))
    {su : rel} (hne : su ≠ 0)
    {gamma : Hmod K (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 := by
  obtain ⟨absEquiv⟩ := absLine
  obtain ⟨modelEquiv⟩ := modelLine
  have hsurj := surjective_of_punctured_acyclicOf hacyclic j i hexact
  subst hgamma
  exact ModuleCat.ne_zero_of_surjective_of_line (rankOneOfIso (exc ≪≫ chartIso) modelEquiv)
    absEquiv hsurj hne

/-- **Step C over a field, with `γ_r` pinned to the Thom class through the section.**
The nonvanishing of the relative Euler class `σ^* u` together with the naturality square
gives `γ_r ≠ 0`.  As over `F₂`, the square trades `hgamma` for six arguments and `hu`, and
`hu` is where the Thom class enters, so an audit of what Step C owes counts `hu` alongside
`hne`. -/
theorem topChernClass_ne_zero_of_su_ne_zero_naturalityOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z)
    {rel chart model HrelE HE : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart) (chartIso : chart ≅ model) (modelLine : Nonempty (model ≃ₗ[K] K))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    {u : HrelE} {gamma : Hmod K (TopCat.of N) twoR}
    (hu : jE.hom u = piStar.hom gamma)
    (hne : sRel.hom u ≠ 0) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_chainOf hacyclic j i hexact absLine exc chartIso modelLine hne
    (topClass_eq_of_naturality' jE j sRel sAbs piStar hnat hsection hu).symm

/-! ## 4. The odd side over a field -/

/-- **Step C's odd side over a field.**  The section's nondegeneracy enters as injectivity
of the chart composite `sRel ≫ t`; with the naturality square, a nonzero Thom class gives
`γ_r ≠ 0`. -/
theorem topChernClass_ne_zero_oddOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z)
    {rel chart model HrelE HE W : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart) (chartIso : chart ≅ model) (modelLine : Nonempty (model ≃ₗ[K] K))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    (t : rel ⟶ W) (hinj : Function.Injective (sRel ≫ t).hom)
    {u : HrelE} (hu : u ≠ 0) {gamma : Hmod K (TopCat.of N) twoR}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_su_ne_zero_naturalityOf hacyclic j i hexact absLine exc chartIso
    modelLine jE sRel sAbs piStar hnat hsection hclass
    (ne_zero_of_injective_compOf sRel t hinj hu)

/-- **The odd side over a field, with the injectivity given by an isomorphism** `e` and the
equation identifying the chart composite with it. -/
theorem topChernClass_ne_zero_odd_isoOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z)
    {rel chart model HrelE HE W : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart) (chartIso : chart ≅ model) (modelLine : Nonempty (model ≃ₗ[K] K))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    (t : rel ⟶ W) (e : HrelE ≅ W) (hcomp : sRel ≫ t = e.hom)
    {u : HrelE} (hu : u ≠ 0) {gamma : Hmod K (TopCat.of N) twoR}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_oddOf hacyclic j i hexact absLine exc chartIso modelLine jE sRel sAbs
    piStar hnat hsection t (injective_of_hom_eq_isoOf (sRel ≫ t) e hcomp) hu hclass

/-- **The odd side over a field, with the injectivity given by a local restriction.**
`res` restricts the bundle pair to a trivialising neighbourhood of the section's zero and
`trivIso` identifies that with the local model; `hsq` says sectioning then charting is
restricting then trivialising.  Only injectivity of `res` is used. -/
theorem topChernClass_ne_zero_odd_localOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z)
    {rel chart model HrelE HE W HlocE : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart) (chartIso : chart ≅ model) (modelLine : Nonempty (model ≃ₗ[K] K))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    (t : rel ⟶ W) (res : HrelE ⟶ HlocE) (trivIso : HlocE ≅ W)
    (hsq : sRel ≫ t = res ≫ trivIso.hom) (hres : Function.Injective res.hom)
    {u : HrelE} (hu : u ≠ 0) {gamma : Hmod K (TopCat.of N) twoR}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_oddOf hacyclic j i hexact absLine exc chartIso modelLine jE sRel sAbs
    piStar hnat hsection t (injective_comp_of_squareOf sRel t res trivIso hsq hres) hu hclass

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms iso_hom_ne_zeroOf
#audit_axioms injective_comp_of_squareOf
#audit_axioms surjective_of_punctured_acyclicOf
#audit_axioms topChernClass_ne_zero_of_chainOf
#audit_axioms topChernClass_ne_zero_of_su_ne_zero_naturalityOf
#audit_axioms topChernClass_ne_zero_oddOf
#audit_axioms topChernClass_ne_zero_odd_isoOf
#audit_axioms topChernClass_ne_zero_odd_localOf

end

end GroupApproximation.CharClass
