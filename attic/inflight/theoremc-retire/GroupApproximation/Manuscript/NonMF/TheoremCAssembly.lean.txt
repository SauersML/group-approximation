import GroupApproximation.GGT.DGOProposition414General
import GroupApproximation.Higman.OmegaSharedProof
import GroupApproximation.Manuscript.NonMF.ChiodoOfHigman
import GroupApproximation.Manuscript.NonMF.HullFillTheoremCCorrected
import GroupApproximation.Manuscript.NonMF.HullInputsProved
import GroupApproximation.Manuscript.NonMF.TheoremCPrinted
import GroupApproximation.GGT.DGOWindmillTheorem53
import GroupApproximation.GGT.ElementaryOsinNormalClosed
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.GGT.HullSCLemma49PowerDiagram
import GroupApproximation.GGT.HullSCFreeProductFactor
import GroupApproximation.GGT.HullSCUnionGeometryAssembly
import GroupApproximation.GGT.HullTheorem316Assembly
import GroupApproximation.GGT.HullYiFiniteFamilyPair
import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.TreeWPDAxis
import GroupApproximation.GGT.DGOTheorem442Proof
import GroupApproximation.GGT.HullYiCyclicProductClosure
import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement
import GroupApproximation.GGT.HullSCLemma44QuasiGeodesicBridge
import GroupApproximation.GGT.RelHypProp23FromHullOsin24
import GroupApproximation.GGT.DGOProposition435HullJoint
import GroupApproximation.GGT.HullSCLemma49PowerDiagramFromComponents
import GroupApproximation.GGT.DGOProposition435JointPrescribed
import GroupApproximation.GGT.VanKampen.Estimating.PieceConstruction
import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea

/-!
# Theorem C assembly

Theorem C is proved from two bundles of cited results: Fournier-Facio's
paragraph (`TheoremC.LiteratureInputs`: Chiodo, Kotowski–Ollivier–Wise,
Fournier-Facio et al. with Osin, Minasyan–Osin, and Hull's common quotient
theorem) and Hull's small cancellation theorem with its companion
(`HullCorrectedInputs.HullInputsCorrected`).

The Hull bundle is the corrected one.  `TorsionFree.HullInputs` is not used
anywhere below `lem:saturation` any more: one of its four fields is false as
recorded, and `Manuscript.NonMF.HullFillKernelRefutation` proves that, so
`Saturation.saturation` and the two printed forms of Theorem C take
`HullCorrectedInputs.HullInputsCorrected` instead.

## This module has no `sorry`

It holds the closed leaves of the assembly, and the two printed statements of
Theorem C over three named hypotheses, the walls of the least-area route:

1. `hgreendlinger : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`,
   Osin's Lemma 4.4 at least-area diagrams;
2. `hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`,
   Osin's Lemma 5.1 in the embedded form;
3. `hKO : TheoremC.KotowskiOllivierStatement`, Kotowski–Kotowski and
   Ollivier–Wise: an infinite finitely presented torsion-free hyperbolic group
   with property (T) (`Hyperbolic.SharpExistence`).

Both bundles are produced from them.  `TorsionFree.hullInputs_of_leastAreaLeaves`
gets Hull's Theorem 7.1 from the least-area one-step theorem
`HullSC.hullOneStepStatement_of_leastAreaLeaves`, and the literature bundle is
`TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`.

## What was retired on 2026-09-13

Until then this module admitted five `sorry`s and assembled
`TheoremC.manuscriptTorsionFreeFullMFRadical_openAdmissions` and
`TheoremC.manuscriptTorsionFreeSimplified_openAdmissions` on them:

* `estimatingSelectionConstruction` and `estimatingUnboundOutput`, two
  propositions of Osin's appendix;
* `relativeIsoperimetricBridgeQuasiGeodesic`, Osin's Lemma 5.1 with its own
  `(1/2,0)`-quasi-geodesic case split;
* `hullRelatorRespelling`, Hull's §6 re-spelling;
* `kotowskiOllivier`.

The first four fed only the Hull chain assembled here:
`hullLemma44FamilyInclusionJoint` through `hullOneStep`, `hullTheorem71` and
`hullInputs`, then `smallCancellationQuotient`, `hullCommonQuotient` and
`literatureInputs`.  Outside this module only the paper's seed,
`MFRecognition.SeedFromTheoremC`, read that chain, and it read it through the
endpoint.  The least-area route produces both bundles the chain produced, from
two leaves in place of four, so the chain is deleted rather than kept alongside
its twin, and the seed reads Theorem C over the three hypotheses instead.

The statements themselves stay in the library; only their admissions are gone:
`GGT.VanKampen.EstimatingSelectionConstructionStatement`,
`GGT.VanKampen.EstimatingUnboundOutputStatement`,
`HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement` and
`HullSC.HullRelatorRespellingStatement`.

`kotowskiOllivier` became the hypothesis `hKO`.  `Kazhdan/KotowskiOllivierClosed.lean`
reduces it to three systolic leaves (`KotowskiOllivierClosed.kotowskiOllivier_of_leaves`),
and `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean` states Theorem C over them.
Neither module is in the root closure, so this one does not import them.  When
the closed `kotowskiOllivier_closed` lands and is wired, `hKO` is spent by one
application.

## The Chiodo field

`ChiodoOfHigman.chiodo_of_omega` proves Chiodo's Theorem 3.10 from Higman's
ω-closure, so the first field of `LiteratureInputs` is discharged down to the
single construction `Higman.Omega.OmegaInput`.  That construction is proved, in
`Higman.OmegaFillLeadLinkBenign`, and read once for the whole repository from
`Higman.OmegaSharedProof`, which the recognition lane imports as well.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF

namespace TorsionFree

open GroupApproximation.HullGeometry

/-! ## Closed leaves of the assembly -/

/-- Dahmani--Guirardel--Osin Proposition 4.14, proved with the
constant uniform in the number of sides (`GGT/DGOLemma421Proof.lean`): in a
weakly relatively hyperbolic group, an isolated component of a quasi-geodesic
polygon has relative length bounded by a constant times the number of sides.
It is the geometric input of Lemma 4.21(b) and of the joint embedding of the
original and selected auxiliary families (`GGT/DGOProposition435JointPrescribed.lean`,
whose hyperbolicity half is the cone-off of the relative Cayley graph along the
selected cyclic subgroups). -/
theorem dgoProposition414Uniform :
    GGT.OsinComponents.DGOProposition414Uniform.{0, 0} :=
  GGT.OsinComponents.dgoProposition414Uniform

/-- Dahmani–Guirardel–Osin, Lemma 4.21(b), derived from uniform Proposition
4.14: the located counting certificate yields separated forward matches, and
the minimal-gap quadrilateral fills the intervening component ranks in
consecutive order. The conclusion retains the two actual basepoints and the
start-coset identities of `GGT/DGOLemma421Statement.lean`. -/
theorem dgoLemma421b : GGT.OsinComponents.DGOLemma421b.{0, 0} :=
  GGT.OsinComponents.dgoLemma421b_of_uniform414 dgoProposition414Uniform

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.dgoProposition414Uniform
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.dgoLemma421b

/-- Hull's Lemmas 5.4–5.6 in the local finite-avoidance form, proved from
DGO Lemma 4.21(b) alone: the orientation-pure detector, the pairwise
non-commensurable triple, the freshening and aggregation steps, the cyclic
product family with its consecutive component match, and the finite
commensurability avoidance are all in `GGT/HullYi*.lean`. -/
theorem hullYiSuitablePairAvoidingFiniteOneSided :
    HullSC.YiSuitablePairAvoidingFiniteOneSided.{0} :=
  HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b dgoLemma421b

/-- Hull's printed all-`m` Corollary 5.7, derived from the local finite-
avoidance producer by the proved finite induction. -/
theorem hullYiSuitableFiniteFamily : HullSC.YiSuitableFiniteFamily.{0} :=
  HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr
    hullYiSuitablePairAvoidingFiniteOneSided

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullYiSuitablePairAvoidingFiniteOneSided
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullYiSuitableFiniteFamily

/-- **Proved** (`GGT/DGOWindmillTheorem53.lean`).  Dahmani–Guirardel–Osin,
*Hyperbolically embedded subgroups and rotating families*, Theorem 5.3(b): for a
separated very rotating family on a hyperbolic geodesic space, every nonidentity
element of the subgroup the rotations generate is conjugate into a rotation
subgroup or is loxodromic.

Three findings put the statement in this shape.

The geodesic hypothesis is not decoration: `GGT/HullSCDGO.lean` shows the
statement without it lets an empty annulus make the very rotating condition
vacuous.  The clauses of the conclusion other than the dichotomy are not cited
at all — `GGT/DGORotatingQuotientResidual.lean` proves the quotient, the map,
its surjectivity and its kernel are `G ⧸ ⟨⟨Rot⟩⟩` and nothing more.  And the
clause this row used to carry alongside the dichotomy, that finite order lifts
with the order preserved, is **not a consequence of Theorem 5.3 and is false as
recorded**: `GGT/DGORotatingQuotientRefutation.lean` refutes it at a
one-point space, where the very rotating condition is vacuous and the clause
asserts that `ℤ` has an element of order two, and
`GGT/DGOFreeSplittingOnePoint.lean` shows the same model satisfies DGO's other
conclusion, the free splitting, so no route from the theorem reaches it.  It is
Hull's §5 and lives with the family he builds, as
`HullSC.RotatingData.finiteOrder_lift`.

Two further restrictions are forced rather than chosen.
`HullSC.eq_one_of_dist_lt_everywhere` refutes a displacement clause stated at
every point of the space — a rotation fixes its apex and lies in the kernel — and
`HullSC.not_rotation_or_loxodromic_of_empty` refutes the dichotomy stated for
every element of the kernel, the identity being neither conjugate into a
rotation subgroup nor loxodromic. -/
theorem dgoTheorem53 : HullSC.DGOQuotientStatementGeodesic.{0, 0} := by
  exact DGOWindmill.dgoQuotientStatementGeodesic

/-- Conversion of a planar exterior arc into the algebraic boundary
contiguity at a supplied word, retaining the source relator rotation.  The
fixed-relator predecessor is refuted by `ExteriorArcCounterexample`; the
rotated statement follows from the region's shelling and short sides. -/
theorem relativeExteriorArcConversionAtWord :
    HullSC.RelativeExteriorArcConversionAtWordRotatedStatement.{0, 0} :=
  HullSC.relativeExteriorArcConversionAtWordRotatedStatement

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.dgoTheorem53
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.relativeExteriorArcConversionAtWord

/-- **Osin, *Acylindrically hyperbolic groups*, Lemma 7.1, proved**
(`GGT.Elementary.osinLemma71_closed`: the Morse theorem, the common-power
theorem and the acylindrical pigeonhole, with no Bowditch dichotomy): an
`s`-normal subgroup of an acylindrically hyperbolic group acts
non-elementarily.  Recorded in the case `lem:saturation` uses it — a normal
subgroup of a torsion-free group — which is also the case the repository's
partial machinery is stated for
(`HullGeometry.exists_escaping_or_noncommuting_of_isSNormal` carries
`IsPowerTorsionFree G`, `HullGeometry.actsNonElementarily_of_normal_conjugate`
carries `[S.Normal]`).
`HullCorrectedInputs.osinNonElementary_of_osinLemma71` checks that this is a
special case of Osin's lemma as it is usually stated. -/
theorem osinLemma71 :
    ∀ {G : Type} [Group G] (A : HullGeneratingSet G),
      IsPowerTorsionFree G → ∀ (N : Subgroup G) [N.Normal],
        HullSuitable.IsSNormal N →
          ActsNonElementarily N (Cayley.base A.alphabet) :=
  GGT.Elementary.osinLemma71_closed

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.osinLemma71

/-! ## Hull's small cancellation theorem over the least-area leaves -/

/-- **Hull, *Small cancellation in acylindrically hyperbolic groups*, Theorem
7.1**, in the finite-set formulation the manuscript records, together with the
manuscript's remark on his construction: the kernel of `q` is normally
generated by `m` elements.  The remark is a field of the quotient
(`HullCorrectedInputs.HullQuotientNG`) because it is a property of the
construction rather than of an arbitrary quotient with the printed properties.

It rests on the two least-area leaves and nothing else:

* `HullSC.hullOneStepStatement_of_leastAreaLeaves` — Theorem 7.1 at `m = 1`,
  from Osin's Lemma 4.4 at least-area diagrams and the embedded Lemma 5.1
  (`GGT/HullSCLemma44BoundedLeastAreaCanonical.lean`).
* `HullSC.hullBallFormNG_of_oneStep` — the induction on `m`, whose kernel
  arithmetic is `HullSC.ker_comp_eq` and whose radius bookkeeping is
  `HullSC.image_cayleyBall_subset`.
* `HullCorrectedInputs.smallCancellation_of_ballFormNG` — the published
  injectivity-radius form turned into the finite-set form. -/
theorem hullTheorem71_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    ∀ {G : Type} [Group G] [IsAcylindricallyHyperbolic G]
      (_hG : IsPowerTorsionFree G) (A : HullGeneratingSet G) {N : Subgroup G},
        Suitable A.alphabet N →
        ∀ {m : ℕ} (t : Fin m → G) {F : Set G}, F.Finite →
          Nonempty (HullCorrectedInputs.HullQuotientNG N t F) := by
  intro G _ _ hG A N hN m t F hF
  exact HullCorrectedInputs.smallCancellation_of_ballFormNG
    (HullSC.hullBallFormNG_of_oneStep
      (HullSC.hullOneStepStatement_of_leastAreaLeaves hgreendlinger hbridge))
    hG A hN t hF

/-- Hull's inputs over the least-area leaves: Theorem 7.1 above, and Osin's
Lemma 7.1, which is closed.  Hull's Corollary 5.7 with Lemma 5.8 is not a field
of the corrected bundle — over a torsion-free ambient group it is
`Manuscript.NonMF.HullInputsProved.exists_pair_suitable_of_torsionFree`, and
that is the only case `lem:saturation` uses. -/
def hullInputs_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullCorrectedInputs.HullInputsCorrected.{0} where
  smallCancellation := hullTheorem71_of_leastAreaLeaves hgreendlinger hbridge
  osinNonElementary := osinLemma71

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullTheorem71_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullInputs_of_leastAreaLeaves

end TorsionFree

namespace TheoremC

/-! ## Chiodo's Theorem 3.10, reduced to Higman's ω-closure -/

/-- **Chiodo, Theorem 3.10 (= Belegradek, Theorem A.1)**, on the ω-closure
rather than on a citation of its own: `chiodo_of_omega` proves it outright from
Higman's ω-closure, and the ω-closure is `Higman.OmegaSharedProof.omegaInput`, the
repository's single record of that construction. -/
theorem chiodo : ChiodoBelegradek.Statement :=
  chiodo_of_omega Higman.OmegaSharedProof.omegaInput

/-! ## The closed citations of Fournier-Facio's paragraph -/

/-- **Proved.**  Osin, *Acylindrically hyperbolic groups*, Theorem 1.2, in the
implication `(AH₃) ⇒ (AH₁)`: a group that is not virtually cyclic and acts on a
hyperbolic space with a loxodromic WPD element is acylindrically hyperbolic.
This is the theorem Minasyan–Osin cite as their Theorem 3.3, and after
`GGT/TreeWPDAxis.lean` it is all that is left of their tree criterion at `E`.
`GGT.osinTheorem12_of` splits it into Dahmani–Guirardel–Osin's Theorem 6.8 and
Osin's `(AH₄) ⇒ (AH₁)`. -/
theorem osinTheorem12 : GGT.OsinTheorem12.{0, 0} :=
  GGT.Elementary.osinTheorem12_unconditional

/-- **Minasyan–Osin at `E`, no longer a citation of its own.**  The tree half is
proved: `E` acts on the Bass–Serre tree of its second HNN splitting, `u₂u₁⁻¹` is
loxodromic on it and satisfies the WPD condition by Minasyan–Osin's Corollary
4.3 — which `GGT/TreeWPDAxis.lean` proves, in the form that asks for the
basepoint to lie on the axis — and `E` is never virtually cyclic.  So the
`(AH₃)` datum of `E` is unconditional and the citation reduces to Osin's
Theorem 1.2. -/
theorem minasyanOsin : MinasyanOsinStatement :=
  GGT.BassSerreDoubleHNN.minasyanOsinStatement_of_osinTheorem12 osinTheorem12

/-- **Proved.**  The last clause of Hull's Corollary 7.4: the Cayley graph of
`E * H₀` over the union of two Hull alphabets is hyperbolic and the translation
action on it is acylindrical.  Hyperbolicity is the four-point condition on
the syllable normal form (`GGT/HullSCUnionGeometryCoprod`), acylindricity is
the branch-point estimate with constant zero together with the factors' own
acylindricity at a long syllable (`GGT/HullSCUnionGeometryAssembly`); the
naive tree inequality this replaces is refuted in
`GGT/HullSCUnionGeometryAcylindrical`. -/
theorem hullFreeProductUnionGeometry : HullSC.FreeProductUnionGeometryStatement :=
  HullSCUnionGeometry.freeProductUnionGeometryStatement_unconditional

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.chiodo
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.osinTheorem12
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.minasyanOsin
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.hullFreeProductUnionGeometry

/-! ## Theorem C over the three least-area hypotheses -/

/-- **Theorem C (`thm:torsion-free`), in radical form**, over `hgreendlinger`,
`hbridge` and `hKO` and nothing else: Hull's bundle is
`TorsionFree.hullInputs_of_leastAreaLeaves`, and the literature bundle is
`TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`.  No
`hW` binder appears, because `manuscriptTorsionFreeFullMFRadical` takes the two
bundles and nothing else.

It replaces `manuscriptTorsionFreeFullMFRadical_openAdmissions`, which rested on
this module's former five `sorry`s.  `MFRecognition.SeedFromTheoremC` reads it to
define the paper's `E`. -/
theorem manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : KotowskiOllivierStatement) : PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical
    (TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves
      hgreendlinger hbridge hKO)
    (TorsionFree.hullInputs_of_leastAreaLeaves hgreendlinger hbridge)

/-- **Theorem C, in the simplified printed statement**, over the same three
hypotheses, reached by the same two bundles.  It replaces
`manuscriptTorsionFreeSimplified_openAdmissions`. -/
theorem manuscriptTorsionFreeSimplified_of_leastAreaInputs
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : KotowskiOllivierStatement) : PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified
    (TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves
      hgreendlinger hbridge hKO)
    (TorsionFree.hullInputs_of_leastAreaLeaves hgreendlinger hbridge)

#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs
#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaInputs

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
