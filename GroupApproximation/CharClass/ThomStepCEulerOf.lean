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
Step C restates against the forms below.

## Main declarations

* `surjective_of_punctured_acyclicOf` — step 1, over any commutative ring.
* `iso_hom_ne_zeroOf` — an isomorphism does not kill a nonzero class.  This replaces
  `hsu_of_ne_zero`, whose generator identification is special to `F₂`.
* `topChernClass_ne_zero_of_chainOf` — steps 1–3 over a field.
* `topChernClass_ne_zero_of_su_ne_zero_naturalityOf` — the same with `γ_r` pinned to the
  Thom class through the section; the form to restate against.
-/

set_option autoImplicit false

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. An isomorphism does not kill a nonzero class -/

/-- **The replacement for `hsu_of_ne_zero`.**  Over `F₂` a nonzero class of the local model
is the generator.  Over a field it is only a unit multiple of one, and no consumer needs
more than that it is nonzero, which any isomorphism preserves. -/
theorem iso_hom_ne_zeroOf {R : Type} [Ring R] {M M' : ModuleCat.{0} R} (e : M ≅ M')
    {x : M} (hx : x ≠ 0) : e.hom.hom x ≠ 0 := by
  intro h
  refine hx ?_
  have h1 := congrArg e.inv.hom h
  rw [← ModuleCat.comp_apply, e.hom_inv_id, map_zero] at h1
  simpa using h1

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
(transported from the local model `loc` along `exc ≪≫ chartIso`) and the absolute group is
a line. -/
theorem topChernClass_ne_zero_of_chainOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z) {rel chart loc : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart) (chartIso : chart ≅ loc) (locLine : Nonempty (loc ≃ₗ[K] K))
    {su : rel} (hne : su ≠ 0)
    {gamma : Hmod K (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 := by
  obtain ⟨absEquiv⟩ := absLine
  obtain ⟨locEquiv⟩ := locLine
  have hsurj := surjective_of_punctured_acyclicOf hacyclic j i hexact
  subst hgamma
  exact ModuleCat.ne_zero_of_surjective_of_line (rankOneOfIso (exc ≪≫ chartIso) locEquiv)
    absEquiv hsurj hne

/-- **Step C over a field, with `γ_r` pinned to the Thom class through the section.**
The form to restate against: the nonvanishing of the relative Euler class `σ^* u` together
with the naturality square gives `γ_r ≠ 0`.  As over `F₂`, the square trades `hgamma` for
six arguments and `hu`, and `hu` is where the Thom class enters, so an audit of what Step C
owes counts `hu` alongside `hne`. -/
theorem topChernClass_ne_zero_of_su_ne_zero_naturalityOf {K : Type} [Field K]
    (hacyclic : PuncturedAcyclicOf K N twoR z)
    {rel chart loc HrelE HE : ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (i : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : rel ≅ chart) (chartIso : chart ≅ loc) (locLine : Nonempty (loc ≃ₗ[K] K))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel) (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    {u : HrelE} {gamma : Hmod K (TopCat.of N) twoR}
    (hu : jE.hom u = piStar.hom gamma)
    (hne : sRel.hom u ≠ 0) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_chainOf hacyclic j i hexact absLine exc chartIso locLine hne
    (topClass_eq_of_naturality' jE j sRel sAbs piStar hnat hsection hu).symm

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms iso_hom_ne_zeroOf
#audit_axioms surjective_of_punctured_acyclicOf
#audit_axioms topChernClass_ne_zero_of_chainOf
#audit_axioms topChernClass_ne_zero_of_su_ne_zero_naturalityOf

end

end GroupApproximation.CharClass
