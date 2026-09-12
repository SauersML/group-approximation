import GroupApproximation.Analysis.LanceForward
import GroupApproximation.Analysis.NuclearQuotient
import GroupApproximation.Analysis.WitnessGroupNonamenable
import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedSurjection
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarNotNuclear
import GroupApproximation.Meta.AxiomGuard

/-!
# The nonnuclearity sentence for the sofic witness `W`

## The printed sentence

`non_mf_groups_exist.tex`, line 271 (anchor string "is not nuclear, since"):

> here `C^*_{\max}(W)` is not nuclear, since `W` is not amenable.

## What is unconditional

* **`W` is not amenable** — `Analysis/WitnessGroupNonamenable`, from the copy of
  the infinite Kazhdan group `ℤ³ ⋊ SL₃(ℤ)` inside `W`.
* **Lance's theorem in the hard direction, at the corpus-wide nuclearity
  predicate** — `Analysis/LanceForward`, for every discrete group and with no
  hypothesis.  This discharges the standing binder
  `TranslationCPAPReductionInput` of `ReducedCStarNotNuclear`, so
  `manuscriptReducedCStarNotNuclear` becomes a theorem, both at the
  manuscript's rank-twelve group `H` and here.
* Consequently **`C^*_λ(W)` is not nuclear**, at
  `CStarExactness.IsNuclearCStarAlgebra`, with no hypothesis at all.

## What is still conditional, and on exactly what

The printed sentence is about `C^*_{\max}(W)`, not `C^*_λ(W)`, and the step
from one to the other is **not** among the facts the quarantine record listed
as missing.  It is:

> nuclearity passes to quotients.

The canonical map `C^*_{\max}(W) → C^*_λ(W)` is a surjective ⋆-homomorphism
(`maximalGroupCStarToReduced_surjective`), so the sentence follows from that
permanence property and from nothing else.  At the approximation-property
definition used here, that permanence property is the Choi--Effros lifting
theorem, and it is **not proved in this repository**.

Two natural attempts to route around it fail, and they are recorded here.  A
third route does work and is not a quotient argument at all: see the note after
the list.

* *Descending the approximation.*  Given completely positive contractions
  `α : C^*_{\max}(W) → D` and `β : D → C^*_{\max}(W)` with `β ∘ α ≈ id` on the
  generating unitaries, the quotient needs a completely positive `α'` on
  `C^*_λ(W)` with `α'(λ_g) ≈ α(u_g)`.  The obvious way to get one is to send a
  finite combination of translations back to the same combination of universal
  unitaries, and for a nonamenable group that map is not even positive: some
  self-adjoint `a = Σ c_g λ_g` has `‖a‖_λ < ‖a‖_max`, so `‖a‖_λ · 1 - a` is
  positive in the reduced algebra and not in the maximal one.  The two positive
  cones differ on exactly that operator system, which is what
  `C^*_{\max} ≠ C^*_λ` means.
* *Running the hypertrace form of Lance's argument at the maximal algebra.*  That
  invariant mean is built from a unital completely positive map
  `B(ℓ²G) → L(G)`, and any covariant pair for the action of `G` on `ℓ^∞(G)` has
  its unitary part weakly contained in the left regular representation.  So no
  faithful representation of `C^*_{\max}(W)` sits inside such a system.

The route that works never extends a map to `B(ℓ²G)`: the approximation maps of
`C^*_{\max}(G)` give a positive-definite matrix kernel `g ↦ down(u_g)` and a Choi
factorization of `up`, the canonical trace turns them into correlations of
finitely supported vectors, and a Reiter vector built from those correlations is
almost invariant (`Analysis/LanceMaximalReiter`, `Analysis/LanceMaximalNuclear`).
`NuclearCStarQuotientInput` stays unproved and is still the hypothesis of
`manuscriptMaximalCStarWNotNuclear_of_quotient` below, carried in the type as a
**named proposition quantified over all C⋆-algebras and all surjections**; the
printed sentence no longer depends on it.

## Manuscript status

The clause "`W` is not amenable" is carried, hypothesis-free.  In this module
the clause "`C^*_{\max}(W)` is not nuclear" is carried only over
`NuclearCStarQuotientInput`, and `manuscriptMaximalCStarWNotNuclear_of_quotient`
must not be badged.  **The printed clause itself is now closed elsewhere**:
`Manuscript/OneSidedMFRadical/MaximalCStarWNotNuclearUnconditional` proves it with
no hypothesis, from Lance's theorem at the maximal algebra
(`Analysis/LanceMaximalNuclear`), which needs no quotient permanence.  The
unconditional non-nuclearity proved here is about `C^*_λ(W)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Amenability CStarExactness ReducedGroupCStarTrace
open LiteralNonMFLinearWitness

-- (universes for the quotient inputs are taken from `Analysis/NuclearQuotient`)

/-! ## The standing reduction, discharged -/

/-- **`TranslationCPAPReductionInput` is a theorem.**  For every discrete
group, the corpus-wide completely positive approximation property of the
reduced C⋆-algebra implies the translation-tested unital form. -/
theorem translationCPAPReduction : TranslationCPAPReductionInput :=
  fun Γ _ hnuc ↦ nuclearReducedCPAP_of_isNuclearCStarAlgebra Γ hnuc

/-- **Lance's theorem, hard direction, at the corpus-wide definition**, as the
named proposition `ReducedCStarNotNuclear` left standing. -/
theorem nuclearImpliesAmenable : NuclearImpliesAmenableInput :=
  nuclearImpliesAmenableInput_of_translationCPAPReductionInput
    translationCPAPReduction

/-- **The rank-twelve endpoint, unconditionally.**  `C⋆_λ(H)` for
`H = EL₁₂(L_{𝔽₂}(1,2))` is not nuclear at the corpus-wide approximation
property; the binder `manuscriptReducedCStarNotNuclear` carried is now
discharged. -/
theorem manuscriptRankTwelveReducedCStarNotNuclear :
    ¬ IsNuclearCStarAlgebra (ReducedGroupCStar RankTwelveEndpoint.H) :=
  manuscriptReducedCStarNotNuclear translationCPAPReduction

/-! ## The reduced algebra of the sofic witness -/

/-- **`C⋆_λ(W)` is not nuclear**, at `CStarExactness.IsNuclearCStarAlgebra`
and with no hypothesis: `W` contains an infinite Kazhdan group, so it is not
amenable, and a nonamenable discrete group has a non-nuclear reduced
C⋆-algebra. -/
theorem witnessGroupReducedCStar_not_isNuclearCStarAlgebra :
    ¬ IsNuclearCStarAlgebra (ReducedGroupCStar WitnessGroup) :=
  not_isNuclearCStarAlgebra_reducedGroupCStar_of_not_isAmenable WitnessGroup
    WitnessGroupNonamenable.witnessGroup_not_isAmenable

/-- The same for the translation-tested property, which is the reading in
which the sofic group's non-nuclearity was previously recorded. -/
theorem witnessGroup_not_nuclearReducedCPAP :
    ¬ NuclearReducedCPAP WitnessGroup := fun h ↦
  WitnessGroupNonamenable.witnessGroup_not_isAmenable
    (nuclearReducedCPAP_iff_isAmenable.mp h)

/-- **`C⋆_λ(E)` is not nuclear**, unconditionally and at the corpus-wide
predicate.

`Sofic/TikuisisWhiteWinterSharpness.markedGroup_reducedGroupCStar_not_isNuclear_of_twwInput`
reaches the same conclusion over Tikuisis--White--Winter and a universal
coefficient theorem for that one algebra.  Neither input is needed: `E` is
nonamenable (`NuclearityAmenability.markedGroup_not_isAmenable`), and that is
enough. -/
theorem markedGroupReducedCStar_not_isNuclearCStarAlgebra :
    ¬ IsNuclearCStarAlgebra
      (ReducedGroupCStar LiteralNonMFPresentation.MarkedGroup) :=
  not_isNuclearCStarAlgebra_reducedGroupCStar_of_not_isAmenable
    LiteralNonMFPresentation.MarkedGroup
    NuclearityAmenability.markedGroup_not_isAmenable

/-! ## The maximal algebra, over the one permanence property that is missing -/

/-- **The canonical map `C^*_{\max}(W) → C^*_λ(W)` is onto.**  Recorded here
because it is the only group-theoretic input the printed sentence needs beyond
nonamenability. -/
theorem maximalToReduced_surjective_witnessGroup :
    Function.Surjective (maximalGroupCStarToReduced WitnessGroup) :=
  MFRecognition.HNNPermanence.maximalGroupCStarToReduced_surjective
    WitnessGroup

/-- **The printed sentence, over the quotient permanence property alone.**

`C^*_{\max}(W)` is not nuclear.  Everything except `NuclearCStarQuotientInput`
is a theorem of this repository: the quotient map onto `C^*_λ(W)` is onto, `W`
is not amenable, and a nonamenable group has a non-nuclear reduced algebra.

The hypothesis is a **leading binder** by design, following the convention of
`ReducedCStarNotNuclear`: a conditional row keeps its hypothesis in front,
because `#audit_closed_axioms` reads the elaborated head and a folded
hypothesis would pass the unconditionality gate dishonestly.  No manuscript
badge may point here.

`Analysis/NuclearQuotient` records a sufficient condition,
`CPCLocalLiftingInput`, and proves the composition around it; that condition is
*not* a known theorem, so nothing at manuscript level is stated over it. -/
theorem manuscriptMaximalCStarWNotNuclear_of_quotient
    (quotientNuclear : NuclearCStarQuotientInput.{1, 0}) :
    ¬ IsNuclearCStarAlgebra (MaximalGroupCStar WitnessGroup) := fun hnuc ↦
  witnessGroupReducedCStar_not_isNuclearCStarAlgebra
    (quotientNuclear (MaximalGroupCStar WitnessGroup)
      (ReducedGroupCStar WitnessGroup) inferInstance inferInstance
      (maximalGroupCStarToReduced WitnessGroup)
      maximalToReduced_surjective_witnessGroup hnuc)

/-! ## The unconditional profile -/

/-- **What the nonnuclearity sentence costs, as one closed proposition.**  `W`
is nonamenable in both of the repository's predicates, the canonical map onto
the reduced algebra is onto, and `C⋆_λ(W)` is not nuclear in either of the two
approximation-property readings.

The maximal algebra is deliberately absent: see
`manuscriptMaximalCStarWNotNuclear_of_quotient`. -/
def ManuscriptWitnessNonnuclearityProfile : Prop :=
  ¬ IsAmenable WitnessGroup ∧
    ¬ HasInvariantMean WitnessGroup ∧
      Function.Surjective (maximalGroupCStarToReduced WitnessGroup) ∧
        ¬ NuclearReducedCPAP WitnessGroup ∧
          ¬ IsNuclearCStarAlgebra (ReducedGroupCStar WitnessGroup)

/-- **The profile, hypothesis-free.** -/
theorem manuscriptWitnessNonnuclearityProfile :
    ManuscriptWitnessNonnuclearityProfile :=
  ⟨WitnessGroupNonamenable.witnessGroup_not_isAmenable,
    WitnessGroupNonamenable.witnessGroup_not_hasInvariantMean,
    maximalToReduced_surjective_witnessGroup,
    witnessGroup_not_nuclearReducedCPAP,
    witnessGroupReducedCStar_not_isNuclearCStarAlgebra⟩

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptWitnessNonnuclearityProfile

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.translationCPAPReduction

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptRankTwelveReducedCStarNotNuclear

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.witnessGroupReducedCStar_not_isNuclearCStarAlgebra

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.markedGroupReducedCStar_not_isNuclearCStarAlgebra

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMaximalCStarWNotNuclear_of_quotient

end OneSidedMFRadical
end Manuscript
end GroupApproximation
