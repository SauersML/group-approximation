import GroupApproximation.Analysis.LanceNuclearAmenable
import GroupApproximation.Analysis.PropertyTNonamenable
import GroupApproximation.Leavitt.RankTwelvePropertyT
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# The scope boundary: `C⋆_r(H)` is not nuclear, so the 1994 suggestion is untouched

## What this module is for

`non_mf_groups_exist.tex` answers the **broad** Blackadar--Kirchberg MF problem
negatively, with `H = EL₁₂(L_{𝔽₂}(1,2))`: `C⋆_r(H)` is separable, stably finite
and not MF.  The manuscript's "Relation to prior work" recalls a strictly older
and strictly narrower question -- the 1994 Oberwolfach suggestion of Blackadar
and Kirchberg that every separable **nuclear** stably finite C⋆-algebra might be
NF -- and this module is the machine-checked reason that question is left
exactly where it was.

The reason is not a limitation of the proof; it is a property of the witness.
`H` is infinite and has Kazhdan's property `(T)`, so it is not amenable, so its
reduced C⋆-algebra fails the completely positive approximation property.  A
non-nuclear algebra is not a counterexample to a statement about nuclear
algebras, whatever else is true of it.  Every clause of that sentence is proved
below from theorems already in this repository; none of it is cited.

## What is unconditional here

`manuscriptRankTwelveNonNuclearityProfile` is a closed proposition and a
theorem: `H` is infinite, `H` is not amenable in either of the repository's two
amenability predicates, and `C⋆_r(H)` does not have the completely positive
approximation property in the reading `Analysis/LanceNuclearity` calls
`NuclearReducedCPAP` -- the property tested on the translations `λ_g`, with
unital completely positive maps through `B(ℂᵏ)`.  This is the same reading in
which `non_mf_group_notes.tex` already records non-nuclearity for the sofic
group `E`; nothing had recorded it for the headline group `H`.

The chain, with no input:

* `Leavitt/RankTwelvePropertyT.infinite` -- `H` is infinite, because the
  coefficient ring `L_{𝔽₂}(1,2)` is infinite and the elementary root `e₀₁`
  embeds it;
* `RankTwelveEndpoint.hasKazhdanPropertyT` -- property `(T)` at rank twelve,
  proved from the in-repo rank-three finite-field theorem through the Leavitt
  rank equivalences, so the Ershov--Jaikin-Zapirain citation in the printed text
  is an attribution of priority and not an assumed input;
* `Analysis/PropertyTNonamenable.infinite_kazhdan_not_isAmenable` -- Følner sets
  from an invariant measure against a Kazhdan pair;
* `Analysis/LanceAmenableOverlap.nuclearReducedCPAP_iff_isAmenable` -- Lance's
  theorem, both directions, at `NuclearReducedCPAP`.

## What is conditional here, and on exactly what

The requested endpoint is stated at `CStarExactness.IsNuclearCStarAlgebra`, the
corpus-wide completely positive approximation property, and **that one is not
unconditionally available**, for a reason that has nothing to do with `H`.
`Analysis/LanceNuclearAmenable` proves the forward half of Lance's theorem at
that definition and records, in its module docstring, that the converse is not
proved and is not cheap.  Two facts are missing, neither about groups:

1. `IsNuclearMap` factors the identity through an arbitrary
   `FinDimCStarAlgebra`, while the Arveson extension this repository proves
   extends maps into `B(ℂᵏ)` and nothing else.  Bridging is injectivity of a
   finite-dimensional C⋆-algebra -- Wedderburn plus a completely positive
   retraction -- and neither is formalized.
2. `IsNuclearMap` asks its two maps only to be contractive, while the Arveson
   step under `NuclearReducedCPAP` asks them to be unital.  The standard repair
   conjugates by `(α 1 + δ)^{-1/2}`, which is continuous functional calculus
   work.

So `manuscriptReducedCStarNotNuclear` carries `TranslationCPAPReductionInput` as
an explicit **leading** binder.  That hypothesis is exactly the missing
reduction and nothing else, it is quantified over **every** discrete group, and
it is deliberately not folded into the conclusion's proposition: this
repository's convention is that a conditional row keeps its hypothesis in front,
because `#audit_closed_axioms` reads the elaborated head and a folded hypothesis
would pass the unconditionality gate dishonestly.  `#audit_closed_axioms` is run
below on the unconditional profile only, and it would reject the conditional
endpoint if it were pointed at it.

A premise cooked up for `H` alone cannot meet
`TranslationCPAPReductionInput`: it is the general reduction or nothing.

## What this module does not say

It does not identify the repository's nuclearity predicates with one another.
Three coexist deliberately -- `CStarExactness.IsNuclearCStarAlgebra` (the
completely positive approximation property on arbitrary elements),
`CStarExactness.NuclearReducedCPAP` (the same property on translations, unital),
and `CStarTensor.IsNuclearCStar` (`min = max`) -- and no equivalence among them
is proved anywhere in this development.  Nothing below substitutes one for
another; the unconditional statement names the predicate it is about, and the
conditional statement names the reduction it is missing.

## Manuscript status

Scope only.  This module bounds the reach of the manuscript's answer: the 1994
nuclear/NF suggestion of Blackadar and Kirchberg is **untouched** by this work,
because the witness `C⋆_r(H)` is not a nuclear algebra.  No headline claim
moves, and no ledger row is discharged.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Amenability CStarExactness ReducedGroupCStarTrace

/-! ## The witness is an infinite Kazhdan group -/

/-- **The headline group is infinite.**  `RankTwelveEndpoint.H` and
`elementaryGroup (Fin 12) RankTwelve.Coeff` are the same type up to `abbrev`
unfolding, so the rank-twelve infiniteness theorem applies directly. -/
theorem rankTwelveEndpoint_infinite : Infinite RankTwelveEndpoint.H :=
  RankTwelve.infinite

/-- **The headline group is not amenable**, in the repository's primary
amenability predicate: a left-invariant finitely additive probability measure on
all subsets.  Property `(T)` plus infiniteness, by the Følner argument of
`Analysis/PropertyTNonamenable`. -/
theorem rankTwelveEndpoint_not_isAmenable :
    ¬ IsAmenable RankTwelveEndpoint.H := by
  haveI : Infinite RankTwelveEndpoint.H := rankTwelveEndpoint_infinite
  exact PropertyTNonamenable.infinite_kazhdan_not_isAmenable
    RankTwelveEndpoint.hasKazhdanPropertyT

/-- **The headline group carries no invariant mean.**  The mean predicate is
the stronger of the repository's two, so this follows from the measure form. -/
theorem rankTwelveEndpoint_not_hasInvariantMean :
    ¬ HasInvariantMean RankTwelveEndpoint.H := fun h ↦
  rankTwelveEndpoint_not_isAmenable (isAmenable_of_hasInvariantMean h)

/-! ## Non-nuclearity, unconditionally, at the translation-tested definition -/

/-- **`C⋆_r(H)` does not have the completely positive approximation property**,
in the reading of `Analysis/LanceNuclearity`: no unital completely positive
factorization through a matrix algebra approximates the translations `λ_g`
uniformly on finite sets.

This is Lance's theorem run backwards at `H`.  It is the same reading in which
`non_mf_group_notes.tex` records non-nuclearity for the sofic group `E`. -/
theorem rankTwelveEndpoint_not_nuclearReducedCPAP :
    ¬ NuclearReducedCPAP RankTwelveEndpoint.H := fun h ↦
  rankTwelveEndpoint_not_isAmenable (nuclearReducedCPAP_iff_isAmenable.mp h)

/-- **The scope boundary of the manuscript's answer**, as one closed
proposition: the witness group is infinite, is non-amenable in both of the
repository's amenability predicates, and its reduced C⋆-algebra fails the
translation-tested completely positive approximation property.

Stated as a named proposition with every binder inside it, so that
`#audit_closed_axioms` applies to the theorem below directly. -/
def ManuscriptRankTwelveNonNuclearityProfile : Prop :=
  Infinite RankTwelveEndpoint.H ∧
    ¬ IsAmenable RankTwelveEndpoint.H ∧
      ¬ HasInvariantMean RankTwelveEndpoint.H ∧
        ¬ NuclearReducedCPAP RankTwelveEndpoint.H

/-- **The scope boundary, hypothesis-free.**  Every clause is a theorem of this
repository; nothing here is cited and nothing is assumed. -/
theorem manuscriptRankTwelveNonNuclearityProfile :
    ManuscriptRankTwelveNonNuclearityProfile :=
  ⟨rankTwelveEndpoint_infinite, rankTwelveEndpoint_not_isAmenable,
    rankTwelveEndpoint_not_hasInvariantMean,
    rankTwelveEndpoint_not_nuclearReducedCPAP⟩

/-! ## The endpoint at the corpus-wide definition, over the one missing step -/

/-- **The reduction this repository does not prove.**  From the corpus-wide
completely positive approximation property of `C⋆_λ(Γ)` -- factorization of the
identity through an arbitrary finite-dimensional C⋆-algebra by merely
contractive completely positive maps -- to the translation-tested, unital,
matrix-algebra form of `Analysis/LanceNuclearity`.

Quantified over every discrete group, so no instance of it can be manufactured
for a single group.  What it hides is finite-dimensional injectivity
(Wedderburn plus a completely positive retraction onto a `B(ℂᵏ)` block) and the
contractive-to-unital repair; see the module docstring and the docstring of
`Analysis/LanceNuclearAmenable`. -/
def TranslationCPAPReductionInput : Prop :=
  ∀ (Γ : Type) [Group Γ],
    IsNuclearCStarAlgebra (ReducedGroupCStar Γ) → NuclearReducedCPAP Γ

/-- **Lance's theorem in the hard direction, at the corpus-wide definition.**
From the completely positive approximation property of the reduced algebra of a
discrete group to amenability of the group.

Recorded separately because it is the classical statement the printed text
appeals to; `TranslationCPAPReductionInput` implies it outright, by the proved
equivalence `nuclearReducedCPAP_iff_isAmenable`. -/
def NuclearImpliesAmenableInput : Prop :=
  ∀ (Γ : Type) [Group Γ],
    IsNuclearCStarAlgebra (ReducedGroupCStar Γ) → IsAmenable Γ

/-- The missing reduction implies the classical hard direction, because the
translation-tested property and amenability are already equivalent here. -/
theorem nuclearImpliesAmenableInput_of_translationCPAPReductionInput
    (reduction : TranslationCPAPReductionInput) : NuclearImpliesAmenableInput :=
  fun Γ inst hnuc ↦
    (@nuclearReducedCPAP_iff_isAmenable Γ inst).mp (@reduction Γ inst hnuc)

/-- **The scope statement, at the corpus-wide nuclearity predicate.**

Granting Lance's theorem in the hard direction -- and nothing else -- the
reduced C⋆-algebra of the manuscript's group `H = EL₁₂(L_{𝔽₂}(1,2))` is not
nuclear.  The hypothesis is a leading binder by design: it is the one step the
repository does not prove, it ranges over all discrete groups, and folding it
into the conclusion would let a conditional row pass the unconditionality gate.

Read together with `manuscriptRankTwelveNonNuclearityProfile`, this is the
manuscript's caveat as a machine-checked sentence: the witness is a non-nuclear
algebra, so the 1994 Blackadar--Kirchberg suggestion about separable **nuclear**
stably finite C⋆-algebras is not addressed by the negative answer to the broad
MF problem. -/
theorem manuscriptReducedCStarNotNuclear_of_lance
    (lance : NuclearImpliesAmenableInput) :
    ¬ IsNuclearCStarAlgebra (ReducedGroupCStar RankTwelveEndpoint.H) :=
  fun hnuc ↦ rankTwelveEndpoint_not_isAmenable
    (lance RankTwelveEndpoint.H hnuc)

/-- **The same endpoint over the reduction actually missing from the tree.**
`TranslationCPAPReductionInput` is the exact gap between the corpus-wide
approximation property and the translation-tested one; everything after it is
proved. -/
theorem manuscriptReducedCStarNotNuclear
    (reduction : TranslationCPAPReductionInput) :
    ¬ IsNuclearCStarAlgebra (ReducedGroupCStar RankTwelveEndpoint.H) :=
  manuscriptReducedCStarNotNuclear_of_lance
    (nuclearImpliesAmenableInput_of_translationCPAPReductionInput reduction)

/-- **The forward half, for contrast, is a theorem here.**  If the manuscript's
group were amenable its reduced algebra would be nuclear at the corpus-wide
definition, by `Analysis/LanceNuclearAmenable`.  So the only gap between the
unconditional profile above and the endpoint is the converse, and it is the
converse alone. -/
theorem rankTwelveEndpoint_isNuclearCStarAlgebra_of_isAmenable
    (h : IsAmenable RankTwelveEndpoint.H) :
    IsNuclearCStarAlgebra (ReducedGroupCStar RankTwelveEndpoint.H) :=
  isNuclearCStarAlgebra_reducedGroupCStar_of_isAmenable h

/-! ## Axiom audit

The profile is a named proposition with no leading input, so the strict gate
applies to it.  The conditional endpoints are deliberately not audited with
`#audit_closed_axioms`: they take construction data, and the gate is supposed to
reject them. -/

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptRankTwelveNonNuclearityProfile

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptReducedCStarNotNuclear

end OneSidedMFRadical
end Manuscript
end GroupApproximation
