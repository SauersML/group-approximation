import GroupApproximation.Computability.HereditaryPropertySwitchCompleteness
import GroupApproximation.Computability.SoficMarkov
import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Sofic.SoficPositiveControl

/-!
# Second-level hardness of recognising soficity from a presentation

The arbitrary-seed event-ray compiler of
`Computability.ParametricRecursiveSwitchPresentation` takes any finite
presentation code as its forbidden seed.  Its infinite-domain branch is the
trivial group and its finite-domain branch is exactly the seed group.  So for
any group property that passes to subgroups, holds of the trivial group, and
fails for *some* finitely presented group, recognising that property on
standard recursively enumerated presentation codes is `Π⁰₂`-hard, and
recognising its failure is `Σ⁰₂`-hard.

This file supplies that statement in the form the research program uses, and
then instantiates it at soficity.  The forbidden seed is not a hypothesis
here: `Endpoint.MainResults.exists_finitelyPresented_nonsofic_group` is an
unconditional theorem of this repository, so `soficCode_pi02Hard` and
`nonsoficCode_sigma02Hard` carry no premises at all.

## Research nodes

* `research/arbitrary-forbidden-seed-hereditary-property-switch.md` --- the
  seed-parametric switch whose two branches are `PUnit` and the seed group.
* `research/second-level-rice-theorem-for-local-approximation-properties.md`
  --- the general second-level Rice statement for hereditary approximation
  properties, of which `pi02Hard_of_hereditary` is the hardness half.
* `research/sofic-recognition-two-generator-recursive-is-pi2-complete.md` ---
  the soficity instance.

## Scope

This is the **enumerated-presentation half** only.  The compiler emits
standard recursively enumerated presentation codes
(`EnumeratedPresentationCodes.PresentationCode`, i.e. ordinary partial
recursive programs).  The two-generator bridge and the compiler into *finite*
presentations named by those research nodes are **not** formalized here; the
conditional finite-output statements live in
`HereditaryPropertySwitchCompleteness.FinitePresentationSwitchCompiler`, which
this development does not inhabit.  Accordingly nothing below claims a
`Π⁰₂` upper bound, only hardness.
-/

namespace GroupApproximation
namespace SoficRecognitionSecondLevel

open ArithmeticalHierarchy
open HereditaryPropertySwitchCompleteness
open PresentationCodes

noncomputable section

/-! ## The general hereditary-property statement -/

/-- The switch datum assembled from the three bare hypotheses: heredity along
injections, truth at the trivial group, and one finite presentation code at
which the property fails. -/
def switchDataOfHereditary (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (seed : PresentationCode)
    (hseed : ¬ P (Carrier seed)) : SwitchPropertyData P where
  hereditary := fun f hf hK ↦ hered f hf hK
  trivial := hone
  forbidden := seed
  forbidden_not := hseed

/-- **Second-level hardness for an arbitrary hereditary property.**  A
subgroup-hereditary property which holds of the trivial group and fails at one
finite presentation code is `Π⁰₂`-hard on standard recursively enumerated
presentation codes. -/
theorem pi02Hard_of_hereditary (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (seed : PresentationCode)
    (hseed : ¬ P (Carrier seed)) :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      P (EnumeratedPresentationCodes.Carrier q)) :=
  enumeratedCodeProperty_pi02Hard (switchDataOfHereditary P hered hone seed hseed)

/-- The complementary `Σ⁰₂` hardness, by complementation of the reduction. -/
theorem sigma02Hard_of_hereditary (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (seed : PresentationCode)
    (hseed : ¬ P (Carrier seed)) :
    Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      ¬ P (EnumeratedPresentationCodes.Carrier q)) :=
  pi02Hard_compl (pi02Hard_of_hereditary P hered hone seed hseed)

/-! ## The soficity instance -/

/-- Soficity read as a property of groups in `Type`. -/
abbrev SoficProperty : (H : Type) → [Group H] → Prop := fun H _ ↦ IsSofic H

/-- The trivial group is sofic, being finite. -/
theorem isSofic_punit : IsSofic (PUnit : Type) :=
  isSofic_of_finite PUnit

/-- A nonsofic finite presentation **code**, with no hypotheses.  Theorem C of
this repository supplies a finitely presented nonsofic group, and
`PresentationCodeCompleteness.exists_code_mulEquiv` names it by a code. -/
theorem exists_nonsofic_presentationCode :
    ∃ seed : PresentationCode, ¬ IsSofic (Carrier seed) := by
  obtain ⟨G, groupG, hfp, hns⟩ := exists_finitelyPresented_nonsofic_group
  letI : Group G := groupG
  letI : Group.IsFinitelyPresented G := hfp
  exact SoficMarkov.exists_nonsofic_code hns

/-- **Recognising soficity from a recursively enumerated presentation is
`Π⁰₂`-hard.**  Unconditional: heredity is `isSofic_of_injective`, the
positive branch is `isSofic_punit`, and the forbidden seed comes from
`exists_finitelyPresented_nonsofic_group`. -/
theorem soficCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      IsSofic (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, hseed⟩ := exists_nonsofic_presentationCode
  exact pi02Hard_of_hereditary SoficProperty
    (fun f hf hK ↦ isSofic_of_injective f hf hK) isSofic_punit seed hseed

/-- **Recognising nonsoficity from a recursively enumerated presentation is
`Σ⁰₂`-hard.** -/
theorem nonsoficCode_sigma02Hard :
    Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      ¬ IsSofic (EnumeratedPresentationCodes.Carrier q)) :=
  pi02Hard_compl soficCode_pi02Hard

/-- Both sides at once. -/
theorem sofic_second_level_package :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
        IsSofic (EnumeratedPresentationCodes.Carrier q)) ∧
      Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
        ¬ IsSofic (EnumeratedPresentationCodes.Carrier q)) :=
  ⟨soficCode_pi02Hard, nonsoficCode_sigma02Hard⟩

end

end SoficRecognitionSecondLevel
end GroupApproximation
