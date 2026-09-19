import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Dynamics.ChainCoreDefectPullback
import GroupApproximation.Dynamics.ChainRecurrence
import GroupApproximation.Dynamics.ChainRecurrenceCovering
import GroupApproximation.Leavitt.OneSidedCompressor
import GroupApproximation.Manuscript.ChainCore.CoreMFRadical
import GroupApproximation.Manuscript.NonMF.Full.AmenableCountable.TraceCountable
import GroupApproximation.Manuscript.NonMFSentences.CompressionRadicalClosedEndpoints
import GroupApproximation.Manuscript.NonMFSentences.CoreRingReflection
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Manuscript.NonMFSentences.FullDefectUniversalRoute
import GroupApproximation.Manuscript.NonMFSentences.HeadlineMaximalProperIsometry
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsDisplaysGeneral
import GroupApproximation.Manuscript.NonMFSentences.NormalKazhdanPrintedHypothesis
import GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerExact
import GroupApproximation.Manuscript.OneSidedMFRadical.HSVanishesProducers

/-!
# Audit gate: theorem-level rows the section gates do not cover

`non_mf_groups_exist.tex`, every section.

`Audit.Intro` and `Audit.Sec2`–`Audit.Sec5` were generated from the census of 2026-09-13.  The
census has since gained theorem-, proposition-, corollary- and lemma-level rows whose named
declarations no gate audits.  This module audits each such declaration, so a widened axiom
closure, or a declaration that has been lost or renamed, is a build error here.

* `#audit_closed_axioms` is used on named-proposition endpoints, whose type is a
  `def … : Prop` (or another closed proposition) rather than a leading binder.
* `#audit_axioms` is used on every other carrier.

Each group names its tex line and census row id.  A declaration named by several rows is
audited once, at its first row.  Rows with status `partial` are not gated here, as in the
section gates.
-/

/-! ## L234 `664f4f34b841` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.HeadlineMaximalProperIsometry.manuscriptSentence_headlineMaximalProperIsometry

/-! ## L263 `d4c878a7ac22` (formalized) -/

#audit_axioms GroupApproximation.Full.NM08.PrintedAmenableNonquasidiagonalTraceCountable

/-! ## L366 `3bd1b6ab184a` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.printedFaithfulCoronaMapGivesMF
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.PrintedFaithfulCoronaMapGivesMF

/-! ## L366 `a8e4ac99b640` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.printedAllMFTargetsKillIffAllCoronasKill
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.PrintedAllMFTargetsKillIffAllCoronasKill

/-! ## L586 `c36b6021a802` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.hsVanishes_of_mem_opToHSShadowResidual
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.hsVanishes_of_mem_printedDefect

/-! ## L630 `b0058fab44d8` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerExact.manuscriptPrintedCentralCoronaCornerExact
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerExact.PrintedCentralCoronaCornerExact

/-! ## L661 `7778d54e679f` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptPrintedNormalKazhdanNormalizedHypothesis
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.normalizedHSHypothesis_iff
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.PrintedNormalKazhdanNormalizedHypothesis

/-! ## L812 `c90393ba6292` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.printedTwoCopiesConverse

/-! ## L871 `1eb8329e0e6b` (formalized) -/

#audit_axioms GroupApproximation.OneSidedCompressor.coreEmbedding_range

/-! ## L1031 `017719ec2a80` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.FullDefectUniversalRoute.printedLeavittAlgebraFullDefectRankTwo_byUniversalGroup

/-! ## L1237 `c34115be7c92` (formalized) -/

#audit_axioms GroupApproximation.MFQuotientUnitsDisplaysGeneral.PrintedKOneCountableAbelianMF

/-! ## L1377 `0ae6fc9e199c` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.PrintedChainCoreCoveringPrintedRoute
#audit_axioms GroupApproximation.Dynamics.PrintedChainCoreCovering

/-! ## L1377 `73bd8ac910aa` (formalized) -/

#audit_axioms GroupApproximation.Dynamics.IsWandering

/-! ## L1526 `42c043ef7ab5` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.CoreRingReflection.coreRestrict_surjective
#audit_axioms GroupApproximation.ChainCore.CoreRingReflection.isUniversalQuotients_coreRestrict
#audit_axioms GroupApproximation.ChainCore.CoreRingReflection.killsKernelOfDirectlyFinite_coreRestrict

/-! ## L1526 `43afa4ee3f10` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.CoreRingReflection.isUniversalQuotients_coreRestrict_mapMatrix

/-! ## L1526 `cfbacaa0fffa` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.CoreRingReflection.directlyFinite_iff_of_coreModels

/-! ## L1624 `521214409259` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.CoreMFRadical.coreKernel_eq_relativeElementary
#audit_axioms GroupApproximation.ChainCore.CoreMFRadical.PrintedCoreKernelAndELKill

/-! ## L1624 `e94a545b030a` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.CoreMFRadical.PrintedCoreMFRadical

/-! ## L1631 `84bacecbfa4c` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.CoreMFRadical.elementaryGroupMap_coreRestrict_surjective

/-! ## L1709 `34c348ec46b9` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.PrintedDynamicRankBudget

/-! ## L1709 `3ea1fdec31e9` (formalized) -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.elCoreKernel
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.glCoreKernel
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.unitCoreKernel
