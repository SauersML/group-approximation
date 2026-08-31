import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductGenerator
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNonvanishing

/-!
# The exact target of the `RPnGeneratorIdentification` branch, and its minimal inputs

The third branch of the project (the "`RPnGeneratorIdentification n`" branch) asks
to *construct*, unconditionally (or in the project's positive-dimensional
variant), a term of the multiplicative generator-identification structure

```text
RPnGeneratorIdentification n
```

defined in `RPnCupProductGenerator.lean`. Once such a term `I` exists, every
conditional consequence already proved from `I` becomes unconditional, in
particular the load-bearing top-class nonvanishing `αⁿ ≠ 0` in `Hⁿ(RPⁿ; F₂)`
(`rpAlpha_power_topClass`) and, via `oddMapFixesTopClass_of_generatorIdentification`
plus `finalComparison_topPowerInput` (`RPnActualAlphaPowerNonvanishing.lean`), the
RPⁿ-cohomology side of the final odd-map degree theorem.

This file makes the branch target and its **exact minimal missing inputs**
completely explicit, as genuine build-clean Lean. It introduces no unproved
assumption and no placeholder `Prop`: it merely *names* the goal and the honest
reduction.

## The two minimal missing inputs

Unfolding the structure `RPnGeneratorIdentification n` (three fields:
`monodromy`, `toModel`, `alpha_eq`), inhabiting it is **exactly** equivalent to
supplying the two genuinely-missing mathematical data, together with one
definitional compatibility:

1. `m : MonodromyFunctional n` — the degree-one Hurewicz/UCT datum: a
   `ZMod 2`-valued functional on `H₁(RPⁿ; F₂)` invariant under the homology
   pushforward of every descended odd map (`ConstructRPAlpha.lean`). This is the
   homological avatar of the already-constructed surjective abelianized monodromy
   character `classifyingHomAb` (`MonodromyCharacter.lean`); it needs the
   Hurewicz identification `H₁(RPⁿ; F₂) ≅ (π₁ RPⁿ)^{ab} ⊗ F₂`, still absent from
   pinned Mathlib.

2. `Φ : RPnCohomologyToModelHom n` — the model-side half of the cohomology-ring
   isomorphism: a graded ring homomorphism `H^*(RPⁿ; F₂) → F₂[α]/(αⁿ⁺¹)` carrying
   a chosen degree-one class to `modelAlpha n` (`RPnCohomologyRingBridge.lean`).
   This is the genuine cup-product cohomology-ring computation, still absent from
   pinned Mathlib.

The compatibility `Φ.alpha = rpAlpha n m` (the field `alpha_eq`) is *not* a third
piece of missing mathematics: the chosen degree-one class of the ring bridge `Φ`
is free, so any honest construction of `Φ` will be (or can be arranged to be)
built with its `alpha` taken to be the actual monodromy class `rpAlpha n m`.

`rpNGeneratorIdentification_of_inputs` records this reduction once and for all:
the two genuine data plus the (free) compatibility *are* a term of
`RPnGeneratorIdentification n`. The branch is closed precisely when `m` and `Φ`
(with `Φ.alpha = rpAlpha n m`) are constructed.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The exact branch target.** The `RPnGeneratorIdentification` branch is closed
iff this type is inhabited:

```text
rpNGeneratorIdentificationTarget n  :=  RPnGeneratorIdentification n.
```

It is stated as a definitional abbreviation purely to give the branch goal a single
canonical name for the downstream prompts; it carries no new mathematical
content. -/
abbrev rpNGeneratorIdentificationTarget (n : ℕ) : Type :=
  RPnGeneratorIdentification n

/-- **Minimal-inputs constructor for the branch target.** Inhabiting
`RPnGeneratorIdentification n` is *exactly* supplying the two genuine missing data
— a monodromy functional `m` and a model-side ring bridge `Φ` — together with the
(free) compatibility `Φ.alpha = rpAlpha n m`. This is the honest reduction of the
branch to its two remaining mathematical inputs; it adds no assumption beyond the
structure's own fields. -/
def rpNGeneratorIdentification_of_inputs (n : ℕ)
    (m : MonodromyFunctional n) (Φ : RPnCohomologyToModelHom n)
    (h : Φ.alpha = rpAlpha n m) : RPnGeneratorIdentification n :=
  { monodromy := m, toModel := Φ, alpha_eq := h }

@[simp] theorem rpNGeneratorIdentification_of_inputs_monodromy (n : ℕ)
    (m : MonodromyFunctional n) (Φ : RPnCohomologyToModelHom n)
    (h : Φ.alpha = rpAlpha n m) :
    (rpNGeneratorIdentification_of_inputs n m Φ h).monodromy = m := rfl

@[simp] theorem rpNGeneratorIdentification_of_inputs_toModel (n : ℕ)
    (m : MonodromyFunctional n) (Φ : RPnCohomologyToModelHom n)
    (h : Φ.alpha = rpAlpha n m) :
    (rpNGeneratorIdentification_of_inputs n m Φ h).toModel = Φ := rfl

/-- **Inhabiting the branch target reduces to the two genuine inputs.** A
`Nonempty (RPnGeneratorIdentification n)` follows from a monodromy functional and a
ring bridge whose chosen degree-one class is the actual `rpAlpha n m`. This is the
precise statement that prompts 18–35 must discharge to close the branch. -/
theorem nonempty_rpNGeneratorIdentification_of_inputs (n : ℕ)
    (m : MonodromyFunctional n) (Φ : RPnCohomologyToModelHom n)
    (h : Φ.alpha = rpAlpha n m) :
    Nonempty (RPnGeneratorIdentification n) :=
  ⟨rpNGeneratorIdentification_of_inputs n m Φ h⟩

/-- **The full embedding target.** The strengthened branch target asks for the
injective variant `RPnGeneratorIdentificationEmbedding n` (model bridge an
injective graded ring map), which additionally pins the truncation
`αⁿ⁺¹ = 0` of the actual class (`rpAlpha_actual_power_succ_eq_zero`). Its minimal
inputs are the same monodromy functional `m` together with a model-side ring
*embedding* `E : RPnCohomologyRingModelEmbedding n` with `E.alpha = rpAlpha n m`. -/
def rpNGeneratorIdentificationEmbedding_of_inputs (n : ℕ)
    (m : MonodromyFunctional n) (E : RPnCohomologyRingModelEmbedding n)
    (h : E.alpha = rpAlpha n m) : RPnGeneratorIdentificationEmbedding n :=
  { monodromy := m, toModel := E, alpha_eq := h }

/-- **Full additive-and-multiplicative target.** Bundles the generator
identification with the cellular-cochain additive computation
(`RPnCellularCochainStructure n`), giving the `αᵏ`-basis results of
`RPnCupProductGenerator.lean`. Its minimal inputs are the two data of
`rpNGeneratorIdentification_of_inputs` together with the cellular structure. -/
def rpNGeneratorIdentificationWithAdditive_of_inputs (n : ℕ)
    (m : MonodromyFunctional n) (Φ : RPnCohomologyToModelHom n)
    (h : Φ.alpha = rpAlpha n m) (c : RPnCellularCochainStructure n) :
    RPnGeneratorIdentificationWithAdditive n :=
  { identification := rpNGeneratorIdentification_of_inputs n m Φ h
    cochain := c }

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
