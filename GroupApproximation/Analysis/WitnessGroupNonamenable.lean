import GroupApproximation.Analysis.NuclearityAmenability
import GroupApproximation.Meta.AxiomGuard

/-!
# The sofic witness group `W` is not amenable

## The printed sentence

`non_mf_groups_exist.tex` (line 271 at the time of writing; navigate by the
anchor string "is not nuclear, since") says of the sofic non-MF group `W` of
Theorem `thm:amenable-trace`:

> here `C^*_{\max}(W)` is not nuclear, since `W` is not amenable.

That sentence has two clauses.  **This module proves the second one and only
the second one**: `W` is not amenable, in both of the repository's amenability
predicates.  It proves nothing about nuclearity of `C^*_{\max}(W)`; see
`Manuscript/OneSidedMFRadical/ReducedCStarNotNuclear.lean` for the standing
record of what the nuclearity clause still costs, and the module docstring
below for why the two are not the same distance away.

## The route, and why it is the manuscript's

The manuscript's reason is that `W` contains `\bar\Gamma = ℤ³ ⋊ SL₃(ℤ)`, which
is infinite and has property `(T)`.  In the formal development the copy is
produced by the level-zero map `iotaAmbient` of the marked-compression
telescope, and the group placed inside is the literal twenty-relator base
`\mathcal B`, which `LiteralBaseCompleteness.affineQuotient_injective`
identifies with the affine matrix group `gammaBar` — so the subgroup exhibited
here *is* `\bar\Gamma`, reached through the presentation that carries the
property-`(T)` certificate.

Concretely, `NuclearityBaseEmbedding.witnessHom_comp_baseMap` factors the
composite

    𝓑  --baseMap-->  E  --witnessHom-->  W

as

    𝓑  --affineQuotient-->  \bar\Gamma  --iotaAmbient-->  W ,

and both legs of the lower route are injective.  Nonamenability is then the
repository's own theorem `PropertyTNonamenable.infinite_kazhdan_not_isAmenable`
transported along the embedding, exactly as
`NuclearityAmenability.markedGroup_not_isAmenable` does for `E`.

Nothing here is cited: infiniteness of the base is
`NuclearityAmenability.infinite_base`, property `(T)` of the base is
`LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT`, and the Følner
argument against a Kazhdan pair is `Analysis/PropertyTNonamenable`.

## Manuscript status

Carries the clause "`W` is not amenable" of the nonnuclearity sentence,
hypothesis-free.  The clause "`C^*_{\max}(W)` is not nuclear" is **not**
carried by anything here and must not be badged from this module.
-/

namespace GroupApproximation
namespace WitnessGroupNonamenable

open Amenability ExplicitLinearModel LiteralNonMFPresentation MarkedCompression
open LiteralNonMFLinearWitness LiteralBaseAffineQuotient

/-! ## The affine matrix base inside the witness group -/

/-- **The literal base embeds in the witness group.**  The composite
`𝓑 → E → W` is injective, because it agrees with `𝓑 → \bar\Gamma → W` and both
of those are injective — the first by completeness of the twenty-relator
presentation, the second because the level-zero copy survives the telescope
and the adjunction of the Clifford lamps. -/
theorem witnessBaseMap_injective :
    Function.Injective (witnessHom.comp baseMap) := by
  rw [NuclearityBaseEmbedding.witnessHom_comp_baseMap, MonoidHom.coe_comp]
  exact (iotaAmbient_injective alpha conjD_injective).comp
    LiteralBaseCompleteness.affineQuotient_injective

/-- The affine matrix group `\bar\Gamma = ℤ³ ⋊ SL₃(ℤ)` is infinite: the literal
base is infinite and maps into it injectively. -/
theorem infinite_gammaBar : Infinite ↥gammaBar := by
  haveI := NuclearityAmenability.infinite_base
  exact Infinite.of_injective affineQuotient
    LiteralBaseCompleteness.affineQuotient_injective

/-- **`\bar\Gamma` is not amenable.**  It is an infinite group with property
`(T)`; the certificate is the one carried by the presented base, transported
along the isomorphism onto the matrix realization. -/
theorem gammaBar_not_isAmenable : ¬ IsAmenable ↥gammaBar :=
  NuclearityAmenability.not_isAmenable_of_base_embeds affineQuotient
    LiteralBaseCompleteness.affineQuotient_injective

/-! ## The witness group -/

/-- **`W` is not amenable**, in the repository's primary amenability
predicate — a left-invariant finitely additive probability measure on all
subsets of the group.

This is the manuscript's stated reason for the nonnuclearity of
`C^*_{\max}(W)`, proved with no hypothesis: `W` contains the infinite Kazhdan
group `\bar\Gamma`, and an infinite Kazhdan group is not amenable. -/
theorem witnessGroup_not_isAmenable : ¬ IsAmenable WitnessGroup :=
  NuclearityAmenability.not_isAmenable_of_base_embeds (witnessHom.comp baseMap)
    witnessBaseMap_injective

/-- **`W` carries no invariant mean on its bounded functions.**  The mean
predicate is the stronger of the repository's two amenability notions, and it
is the one Lance's theorem consumes. -/
theorem witnessGroup_not_hasInvariantMean : ¬ HasInvariantMean WitnessGroup :=
  NuclearityAmenability.not_hasInvariantMean_of_base_embeds
    (witnessHom.comp baseMap) witnessBaseMap_injective

/-! ## The manuscript clause -/

/-- **The nonamenability clause of the nonnuclearity sentence**, as a named
proposition with every quantifier inside it: the literal base embeds in `W`,
that base is infinite and Kazhdan, and `W` is nonamenable in both senses.

The nuclearity clause of the printed sentence is deliberately absent. -/
def ManuscriptWitnessGroupNotAmenable : Prop :=
  Function.Injective (witnessHom.comp baseMap) ∧
    Infinite LiteralNonMFPresentation.Base ∧
      HasKazhdanPropertyT.{0, 0} LiteralNonMFPresentation.Base ∧
        ¬ IsAmenable WitnessGroup ∧
          ¬ HasInvariantMean WitnessGroup

/-- **"`W` is not amenable", hypothesis-free.** -/
theorem manuscriptWitnessGroupNotAmenable : ManuscriptWitnessGroupNotAmenable :=
  ⟨witnessBaseMap_injective, NuclearityAmenability.infinite_base,
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT,
    witnessGroup_not_isAmenable, witnessGroup_not_hasInvariantMean⟩

#audit_closed_axioms
  GroupApproximation.WitnessGroupNonamenable.manuscriptWitnessGroupNotAmenable

end WitnessGroupNonamenable
end GroupApproximation
