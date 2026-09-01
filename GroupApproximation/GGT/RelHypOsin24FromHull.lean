import GroupApproximation.GGT.RelHypOsin24SuitabilityGlue
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.HullHeGXFamily

/-!
# The exact current Hull assembly boundary for Osin's Theorem 2.4

This module records the part of the proposed specialization that follows from
the current Hull interfaces without changing their statements.

`HullLemma44CanonicalQuotientStatement` immediately implies the older
peripheral-preservation-only interface.  Combining the canonical Lemmas 4.4
and 4.9 with the one-sided Yi finite-avoidance theorem gives Hull's one-step
theorem once `HeGXFamily` supplies the simultaneously hyperbolically embedded
elementary closures.

No relator-selection hypothesis occurs: the exact published `C₁` relator is
already constructed unconditionally by
`exists_auxiliaryRelatorOfBaseLetterPublished_exact` in
`HullSCAuxiliaryRelatorPublished`.

The remaining mismatch with the requested Osin theorem is structural rather
than parameter bookkeeping.  The current `AuxiliaryPeripheralFamily` contains
only the finitely many elementary-closure pairs selected inside suitable
subgroups.  It has no slot for Osin's arbitrary original peripheral family,
and `QuotientPeripheralPreservation.injOn_peripheralUnion` consequently ranges
only over those auxiliary pairs.  The countermodel in `RelHypOsin24Glue` also
shows that the current endpoint-only `IsRelativelyHyperbolic` hypothesis cannot
be converted to a labelled `RelGenSet.IsHyperbolicallyEmbedded` input in
general.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- The canonical form of Hull Lemma 4.4 contains the exact preserved-family
interface used by the earlier filling assembly; its additional conclusion is
injectivity on the requested Cayley ball. -/
theorem hullLemma44PreservedPeripheralFamily_of_canonical
    (h44 : HullSC.HullLemma44CanonicalQuotientStatement.{u}) :
    HullSC.HullLemma44PreservedPeripheralFamily.{u} := by
  intro G _ A N k S D
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h44 D 0
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨_hinj, hpreserve⟩ := hgood W q hinput hsurj hker
  exact hpreserve

/-- The exact generic Hull one-step theorem currently assembled in the
repository.  Yi finite avoidance supplies the finite Yi family; `HeGXFamily`
is still required by `simultaneousAuxiliaryPeripheralSelection_of_finiteYi_of_heGX`
to construct one jointly embedded auxiliary family.  Lemmas 4.4 and 4.9 then
assemble the literal one-relator quotient, and the published relator theorem
supplies its `C₁` input with no additional premise. -/
theorem hullOneStepStatement_of_lemma44_of_lemma49_of_yi_of_heGX
    (h44 : HullSC.HullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{u, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{u})
    (hhe : HeGXFamily.{u, 0}) : HullSC.HullOneStepStatement.{u} := by
  have hfiniteYi : HullSC.YiSuitableFiniteFamily.{u} :=
    HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr hyi
  have hselect : HullSC.SimultaneousAuxiliaryPeripheralSelection.{u} :=
    HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_of_heGX
      hfiniteYi hhe
  have hquot : HullSC.TorsionFreeHullCanonicalQuotientStatement.{u} :=
    HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49
      hselect h44 h49
  exact HullSC.AuxiliaryPeripheralFamily.hullOneStep_of_canonicalQuotient hquot

end RelHyp
end GGT
end GroupApproximation
