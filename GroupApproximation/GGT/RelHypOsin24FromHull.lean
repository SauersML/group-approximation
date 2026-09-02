import GroupApproximation.GGT.RelHypOsin24SuitabilityGlue
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.GGT.HullSCLemma44FamilyStatement
import GroupApproximation.GGT.HullYiFiniteFamilyInduction

/-!
# The exact current Hull assembly boundary for Osin's Theorem 2.4

This module records the part of the proposed specialization that follows from
the current Hull interfaces without changing their statements.

`HullLemma44CanonicalQuotientFamilyStatement` specializes to the existing
canonical statement, which immediately implies the older
peripheral-preservation-only interface.  Combining the canonical Lemmas 4.4
and 4.9 with the one-sided Yi finite-avoidance theorem gives Hull's one-step
theorem.  The proved Theorem 3.16 assembly supplies the simultaneously
hyperbolically embedded elementary closures, so no `HeGXFamily` input remains.

No relator-selection hypothesis occurs: the exact published `C₁` relator is
already constructed unconditionally by
`exists_auxiliaryRelatorOfBaseLetterPublished_exact` in
`HullSCAuxiliaryRelatorPublished`.

The family Lemma 4.4 interface is the slot for Osin's arbitrary original
peripheral family.  `RelHypDefinition` now supplies that family as a labelled
finite-base `RelGenSet`, so the remaining assembly work is to combine it with
the selected elementary closures and iterate the tied one-step quotient.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- The canonical form of Hull Lemma 4.4 contains the exact preserved-family
interface used by the earlier filling assembly; its additional conclusion is
injectivity on the requested Cayley ball. -/
theorem hullLemma44PreservedPeripheralFamily_of_family
    (h44family : HullSC.HullLemma44CanonicalQuotientFamilyStatement.{u, 0}) :
    HullSC.HullLemma44PreservedPeripheralFamily.{u} := by
  have h44 : HullSC.HullLemma44CanonicalQuotientStatement.{u} :=
    HullSC.hullLemma44CanonicalQuotientStatement_of_family h44family
  intro G _ A N k S D
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h44 D 0
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨_hinj, hpreserve⟩ := hgood W q hinput hsurj hker
  exact hpreserve

/-- The exact generic Hull one-step theorem from the three shared lane inputs.
Yi finite avoidance supplies the finite Yi family, the proved Theorem 3.16
assembly constructs one jointly embedded auxiliary family, and the family
form of Lemma 4.4 specializes to the current canonical quotient theorem.
Lemma 4.9 and the published relator theorem then complete the literal
one-relator quotient. -/
theorem hullOneStepStatement_of_lemma44family_of_lemma49_of_yi
    (h44family : HullSC.HullLemma44CanonicalQuotientFamilyStatement.{u, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{u, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{u}) :
    HullSC.HullOneStepStatement.{u} := by
  have hfiniteYi : HullSC.YiSuitableFiniteFamily.{u} :=
    HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr hyi
  have hselect : HullSC.SimultaneousAuxiliaryPeripheralSelection.{u} :=
    HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      hfiniteYi
  have h44 : HullSC.HullLemma44CanonicalQuotientStatement.{u} :=
    HullSC.hullLemma44CanonicalQuotientStatement_of_family h44family
  have hquot : HullSC.TorsionFreeHullCanonicalQuotientStatement.{u} :=
    HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49
      hselect h44 h49
  exact HullSC.AuxiliaryPeripheralFamily.hullOneStep_of_canonicalQuotient
    (u := u) hquot

end RelHyp
end GGT
end GroupApproximation
