import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerTopClassAction

/-!
# Construction of `ModTwoTopClassComparison e` (Prompt 15)

This file assembles the second final-theorem branch, the mod-two top-class /
degree comparison `ModTwoTopClassComparison e`, from the genuine, build-clean
outputs of the previous prompts, and simplifies the final odd-map theorem so that
it no longer carries `ModTwoTopClassComparison e` as a *free* assumption.

## The reduction chain (all proved, build-clean)

The branch is fully reduced — through the project's *proved, unconditional*
machinery — to a single named homological datum about the `F₂` top homology of the
sphere:

```text
SphereModTwoTopData e                                   -- bundled F₂ top-homology datum (Prompt 12)
  ──(modTwoTopHomologyScalar_of_data)──▶
ModTwoTopHomologyScalar e                               -- F₂ pushforward scalar action
  ──(modTwoTopClassComparison_of_topHomologyScalar)──▶  -- Kronecker pairing, Prompt 14
ModTwoTopClassComparison e
```

* The first arrow uses the **coefficient-reduction** theory of Prompt 12–13
  (`CoefficientReduction.lean`): the reduced integral top generator, its mod-two
  scalar action `degree_modTwo_action_on_reduced_generator`, and the `2`-torsion
  module structure.
* The second arrow uses the **top-class Kronecker pairing** of Prompt 14
  (`KroneckerTopClassAction.lean`): `cohomology_scalar_eq_homology_scalar` /
  `modTwoTopClassComparison_of_topHomologyScalar_pairing`, i.e. that the cohomology
  top-class action scalar equals the homology generator action scalar.

The declarations in this file package these two arrows into a single named
construction theorem and re-express the final odd-map theorem
(`oddMap_degree_odd_final`) with the comparison discharged from those named
inputs.

## The single remaining named topological input

After this assembly, the *only* genuinely-topological obligation of the branch is
a term of `SphereModTwoTopData e` (equivalently `ModTwoTopHomologyScalar e`,
equivalently the conjunction of the nonvanishing
`SphereTopGeneratorReductionNonvanishing e` and one-dimensionality of
`Hₙ(Sⁿ; F₂)`).  This is the `F₂` sphere top-homology computation
`Hₙ(Sⁿ; F₂) ≅ F₂`, which requires the excision / Mayer–Vietoris / suspension core
still absent from pinned Mathlib `v4.28.0` (the same shared core blocker as the
integral `SphereTopHomologyIso`).  No fake generator, nonvanishing, isomorphism,
or scalar action is introduced here.
-/

open CategoryTheory

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. Construction of `ModTwoTopClassComparison e` from the generator reduction

The bundled datum `SphereModTwoTopData e` (Prompt 12) records exactly the three
remaining homological facts about `Hₙ(Sⁿ; F₂)`: a nonzero spanning generator `g`
and the mod-two degree scalar action of every self-map on `g`.  From it the whole
comparison follows. -/

/-- **`ModTwoTopClassComparison e` from the (unbundled) generator reduction.**

This is the *sharpest combined theorem* of the branch: it derives the mod-two
top-class / degree comparison from exactly the named outputs of the previous
prompts, with the three primitive homological facts about the `F₂` top homology of
the sphere given as explicit arguments rather than bundled:

* `g` — a top class in `Hₙ(Sⁿ; F₂)` (the reduced generator);
* `g_ne` — `g ≠ 0` (the genuine nonvanishing input
  `SphereTopGeneratorReductionNonvanishing`-style);
* `spans` — `g` spans `Hₙ(Sⁿ; F₂)` over `F₂` (one-dimensionality);
* `action` — the `F₂` pushforward of every self-map acts on `g` by the mod-two
  integer degree (Prompt 13 `degree_modTwo_action_on_reduced_generator`-style).

The proof routes through the coefficient-reduction packaging
`modTwoTopClassComparison_of_data`, which itself composes the Prompt-12 reduction
with the Prompt-14 Kronecker-pairing reduction
`modTwoTopClassComparison_of_topHomologyScalar`.  Build-clean. -/
theorem modTwoTopClassComparison_of_generatorReduction {n : ℕ}
    (e : SphereTopHomologyIso n)
    (g : homologyZMod2 (TopCat.of (Sphere n)) n) (g_ne : g ≠ 0)
    (spans : ∀ z, ∃ a : ZMod 2, z = a • g)
    (action : ∀ f : C(Sphere n, Sphere n),
      (homologyPushZMod2 (TopCat.ofHom f) n).hom g = (degreeOfIso e f : ZMod 2) • g) :
    ModTwoTopClassComparison e :=
  modTwoTopClassComparison_of_data e
    { g := g, g_ne := g_ne, spans := spans, action := action }

/-- **`ModTwoTopClassComparison e` from the generator reduction, via the explicit
top-class Kronecker pairing (Prompt 14).**  Identical conclusion to
`modTwoTopClassComparison_of_generatorReduction`, but routing the homology→cohomology
step through the Prompt-14 pairing reduction
`modTwoTopClassComparison_of_topHomologyScalar_pairing`
(`cohomology_scalar_eq_homology_scalar`) rather than
`modTwoTopClassComparison_of_topHomologyScalar`.  This exhibits explicitly the
*coefficient-reduction theorem + top-class pairing theorem ⇒
ModTwoTopClassComparison e* assembly requested by the prompt. -/
theorem modTwoTopClassComparison_of_generatorReduction_pairing {n : ℕ}
    (e : SphereTopHomologyIso n)
    (g : homologyZMod2 (TopCat.of (Sphere n)) n) (g_ne : g ≠ 0)
    (spans : ∀ z, ∃ a : ZMod 2, z = a • g)
    (action : ∀ f : C(Sphere n, Sphere n),
      (homologyPushZMod2 (TopCat.ofHom f) n).hom g = (degreeOfIso e f : ZMod 2) • g) :
    ModTwoTopClassComparison e :=
  modTwoTopClassComparison_of_topHomologyScalar_pairing e
    (modTwoTopHomologyScalar_of_data e
      { g := g, g_ne := g_ne, spans := spans, action := action })

/-- **`ModTwoTopClassComparison e` from the bundled datum.**  The bundled form of
`modTwoTopClassComparison_of_generatorReduction`; definitionally the project's
`modTwoTopClassComparison_of_data`, restated here as the named branch
construction. -/
theorem modTwoTopClassComparison_of_generatorReduction_data {n : ℕ}
    (e : SphereTopHomologyIso n) (d : SphereModTwoTopData e) :
    ModTwoTopClassComparison e :=
  modTwoTopClassComparison_of_data e d

/-! ## 2. Final odd-map theorem with `ModTwoTopClassComparison e` discharged

The final assembly `oddMap_degree_odd_final` (`FinalOddMapComparison.lean`) takes
`ModTwoTopClassComparison e` as a *free* assumption.  Using the construction above
we re-express it so that this free assumption is replaced by the more primitive
named inputs of the previous prompts. -/

/-- **Final odd-map degree theorem, comparison discharged from the bundled
generator datum.**  Same conclusion as `oddMap_degree_odd_final`, but with the
free assumption `ModTwoTopClassComparison e` *removed*: it is supplied by
`modTwoTopClassComparison_of_data` from the bundled `F₂` top-homology datum
`SphereModTwoTopData e` (the Prompt-12 output).  The remaining inputs are exactly
the named outputs of the previous prompts:

* `d : SphereModTwoTopData e` — the `F₂` top-homology datum (Prompt 12);
* `htop : OddMapFixesTopClass n` — the RPⁿ / double-cover descent input. -/
theorem finalComparison_without_modTwoComparison_assumption {n : ℕ}
    (e : SphereTopHomologyIso n) (d : SphereModTwoTopData e)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) :=
  oddMap_degree_odd_final e (modTwoTopClassComparison_of_data e d) htop f hf

/-- **Final odd-map degree theorem, comparison discharged from the top
`F₂`-homology scalar action.**  Variant of
`finalComparison_without_modTwoComparison_assumption` taking the unbundled named
input `ModTwoTopHomologyScalar e` directly (discharged via the Prompt-14 pairing
reduction `modTwoTopClassComparison_of_topHomologyScalar`). -/
theorem finalComparison_of_topHomologyScalar {n : ℕ}
    (e : SphereTopHomologyIso n) (h : ModTwoTopHomologyScalar e)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) :=
  oddMap_degree_odd_final e (modTwoTopClassComparison_of_topHomologyScalar e h) htop f hf

/-- **Final odd-map degree theorem from the unbundled generator reduction.**  The
most explicit form: the comparison is constructed by
`modTwoTopClassComparison_of_generatorReduction` from the three primitive
homological facts, and the RPⁿ descent enters through `htop`.  No free
`ModTwoTopClassComparison e` assumption. -/
theorem finalComparison_of_generatorReduction {n : ℕ}
    (e : SphereTopHomologyIso n)
    (g : homologyZMod2 (TopCat.of (Sphere n)) n) (g_ne : g ≠ 0)
    (spans : ∀ z, ∃ a : ZMod 2, z = a • g)
    (action : ∀ f : C(Sphere n, Sphere n),
      (homologyPushZMod2 (TopCat.ofHom f) n).hom g = (degreeOfIso e f : ZMod 2) • g)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) :=
  oddMap_degree_odd_final e
    (modTwoTopClassComparison_of_generatorReduction e g g_ne spans action) htop f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

