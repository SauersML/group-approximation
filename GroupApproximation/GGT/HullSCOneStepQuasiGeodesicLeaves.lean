import GroupApproximation.GGT.HullSCLemma44QuasiGeodesicBridge
import GroupApproximation.GGT.HullSCLemma49PowerDiagramFromComponents
import GroupApproximation.GGT.HullSCLemma49PowerDiagram
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.GGT.HullSCFillingSelectionTheorem316
import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.HullYiCyclicProductClosure
import GroupApproximation.GGT.DGOLemma421FromUniform414
import GroupApproximation.GGT.DGOProposition414General
import GroupApproximation.GGT.VanKampen.Estimating.PieceConstruction
import GroupApproximation.GGT.HullSCRelativeGreendlingerSpelling
import GroupApproximation.GGT.HullSCRelativeExteriorArcConversion
import GroupApproximation.GGT.HullSC
import GroupApproximation.GGT.ElementaryOsinNormalClosed
import GroupApproximation.Manuscript.NonMF.HullFillCorrectedInputs
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Theorem 7.1 does not need the §6 re-spelling leaf

`non_mf_groups_exist.tex`, `thm:hull` (Hull, *Small cancellation in acylindrically
hyperbolic groups*, Theorem 7.1 (a), (c), (e)) is reached in
`Manuscript/NonMF/TheoremCAssembly.lean` through

`hullOneStep ← hullCanonicalQuotient ← hullLemma44Canonical ← hullLemma44FamilyInclusion
← hullLemma44FamilyInclusionJoint ← hullRelatorRespelling`,

that is, the selected-family Lemma 4.4 is read off the *family* form at the empty original
family, and the family form carries the re-spelling admission
`HullSC.HullRelatorRespellingStatement`.  That detour is unnecessary.
`HullSC.hullLemma44CanonicalQuotientStatement_of_quasiGeodesic` already produces
`HullLemma44CanonicalQuotientStatement` from the certificate at quasi-geodesic boundaries and
Osin's Lemma 5.1 bridge alone: the bridge applies verbatim to the selected family that carries
the relators, so there is nothing to re-spell.

This module assembles the one-relator theorem and the published ball form along that route.
Every step is a landed theorem; the three hypotheses are exactly the three admissions of
`TheoremCAssembly` other than the re-spelling one and `kotowskiOllivier`:

* `GGT.VanKampen.EstimatingSelectionConstructionStatement` (Osin's Lemma 6.5(a) selection),
* `GGT.VanKampen.EstimatingUnboundOutputStatement` (Osin's unbound estimate at his scale),
* `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement` (Osin's Lemma 5.1 with its own case
  split).

So `thm:hull`, `lem:saturation` and the Hull half of `thm:torsion-free` rest on those three.

## Where the re-spelling leaf is still consumed, and what the source does there

The family form is consumed by Osin's Theorem 2.4 (`GGT/RelHypOsin24FromHull.lean`,
`osin24HullStep_of_data`) for Fournier-Facio's Proposition 2.3, which uses the original-family
conjunct `CanonicalQuotientFamilyPreservation` for relative hyperbolicity of the quotient.
Hull does not obtain that conjunct by re-spelling the relators over the original family.  His
Lemma 4.4 is stated for one hyperbolically embedded collection, and in the proof of his
Corollary 7.4 he applies it to the *joint* collection `{⟨f₁⟩, ⟨f₂⟩, ⟨h₁⟩, ⟨h₂⟩}`, of which the
relators are already words; the relator family is read in the joint letters, which is the
index relabelling `HullSC.jointRelatorRespellingStatement_proved` performs.  The original
collection survives as a subcollection, and dropping the auxiliary cyclic members over a finite
enlargement of the base is Proposition 4.35 of Dahmani–Guirardel–Osin in its printed direction.
The uniform `HullSC.OriginalRelatorRespellingStatement` is therefore not a statement of the
source at all.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Hull's Lemma 4.4 for the selected auxiliary family, from the two estimating admissions
and Osin's Lemma 5.1 bridge.**  No re-spelling input occurs: the certificate and the bridge are
applied to the selected family itself. -/
theorem hullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeaves
    (hselection : GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hunbound : GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    HullLemma44CanonicalQuotientStatement.{0} := by
  have hgeom : RelativeGreendlingerQuasiGeodesicSpellingStatement.{0, 0} :=
    relativeGreendlingerQuasiGeodesicSpellingStatement_of_components hselection
      GGT.VanKampen.estimatingPieceConstructionStatement hunbound
      relativeDiscRealizationSpellingStatement
      relativeExteriorArcConversionAtWordRotatedStatement
  exact hullLemma44CanonicalQuotientStatement_of_quasiGeodesic hgeom hbridge

/-- **Hull's Lemma 4.9 in kernel-power form, from the two estimating admissions.**  The piece
construction, the disc realization and the arc conversion are theorems. -/
theorem hullLemma49KernelPowerStatement_of_quasiGeodesicLeaves
    (hselection : GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hunbound : GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0}) :
    HullLemma49KernelPowerStatement.{0, 0} :=
  hullLemma49KernelPowerStatement_of_geodesicPowerDiagram
    (hullLemma49ShortestGeodesicPowerDiagramStatement_of_estimating hselection
      GGT.VanKampen.estimatingPieceConstructionStatement hunbound
      relativeExteriorArcConversionAtWordRotatedStatement)

/-- **Hull's Theorem 7.1 at one relator, with no re-spelling admission.**  The simultaneous
auxiliary selection is proved (uniform Proposition 4.14 → Lemma 4.21(b) → Yi finite avoidance →
Theorem 3.16); Lemma 4.4 is the selected-family form above; Lemma 4.9 is the kernel-power form
above; the exact §6 relator is `exists_auxiliaryRelatorOfBaseLetterPublished_exact`. -/
theorem hullOneStepStatement_of_quasiGeodesicLeaves
    (hselection : GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hunbound : GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    HullOneStepStatement.{0} := by
  have h414 : GGT.OsinComponents.DGOProposition414Uniform.{0, 0} :=
    GGT.OsinComponents.dgoProposition414Uniform
  have h421 : GGT.OsinComponents.DGOLemma421b.{0, 0} :=
    GGT.OsinComponents.dgoLemma421b_of_uniform414 h414
  have hyi : YiSuitablePairAvoidingFiniteOneSided.{0} :=
    yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b h421
  have hselect : SimultaneousAuxiliaryPeripheralSelection.{0} :=
    simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      (yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr hyi)
  have h44 : HullLemma44CanonicalQuotientStatement.{0} :=
    hullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeaves hselection hunbound hbridge
  have h49 : HullLemma49KernelPowerStatement.{0, 0} :=
    hullLemma49KernelPowerStatement_of_quasiGeodesicLeaves hselection hunbound
  exact AuxiliaryPeripheralFamily.hullOneStep_of_canonicalQuotient
    (torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49 hselect h44 h49)

/-- **Hull's Theorem 7.1 in its published ball form, with the kernel datum**, over the same
three admissions: the induction on `m` of `hullBallFormNG_of_oneStep`. -/
theorem hullBallFormNG_of_quasiGeodesicLeaves
    (hselection : GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hunbound : GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    Manuscript.NonMF.HullCorrectedInputs.HullBallFormStatementNG.{0} :=
  hullBallFormNG_of_oneStep
    (hullOneStepStatement_of_quasiGeodesicLeaves hselection hunbound hbridge)

/-- **The corrected Hull bundle consumed by `lem:saturation` and `thm:torsion-free`**, over the
three admissions and no re-spelling: the finite-set form of Theorem 7.1 from the ball form, and
Osin's Lemma 7.1, which is a theorem. -/
def hullInputsCorrected_of_quasiGeodesicLeaves
    (hselection : GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hunbound : GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    Manuscript.NonMF.HullCorrectedInputs.HullInputsCorrected.{0} where
  smallCancellation := by
    intro G _ _ hG A N hN m t F hF
    exact Manuscript.NonMF.HullCorrectedInputs.smallCancellation_of_ballFormNG
      (hullBallFormNG_of_quasiGeodesicLeaves hselection hunbound hbridge) hG A hN t hF
  osinNonElementary := GGT.Elementary.osinLemma71_closed

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.hullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeaves
#audit_axioms GroupApproximation.HullSC.hullLemma49KernelPowerStatement_of_quasiGeodesicLeaves
#audit_axioms GroupApproximation.HullSC.hullOneStepStatement_of_quasiGeodesicLeaves
#audit_axioms GroupApproximation.HullSC.hullBallFormNG_of_quasiGeodesicLeaves
#audit_axioms GroupApproximation.HullSC.hullInputsCorrected_of_quasiGeodesicLeaves
