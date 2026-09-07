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

This module assembles the two printed statements of Theorem C.  Every theorem
used by the assembly has its own declaration, and unfinished proofs remain
ordinary explicit proof holes until their Lean implementations are complete.

## The count went from four to five on purpose

`hullLemma44FamilyInclusionJoint` used to be an admission of its own.  It is now
a theorem, assembled from the two estimating admissions, two proved vk-side
theorems, and two new admissions — Osin's Lemma 5.1 at its own boundary
hypothesis (`relativeIsoperimetricBridgeQuasiGeodesic`) and Hull's §6 relator
re-spelling (`hullRelatorRespelling`).  Four holes became five, and that is an
improvement, for a reason worth stating so that nobody later "fixes" it back.

The old leaf could not be closed by anyone.  Reading it through
`hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_controls`, it
bottomed out in `HullSC.RelativeGreendlingerStatement`, which asks for Osin's
Lemma 4.4 **without the `(lambda,c)`-quasi-geodesic boundary hypothesis the
source states**, at every reduced diagram.  The obligation had been filed
against the wrong lemma: Osin discharges it inside Lemma 5.1, whose proof opens
"Suppose first that `p` is not `(1/2,0)`-quasi-geodesic" and only afterwards
applies Lemma 4.4.  Moving the case split back to Lemma 5.1 — which makes that
statement *stronger*, not weaker, since its hypothesis narrows — puts every
remaining hole on a statement that matches a citable source and that somebody
could in principle prove.  Five named, source-matched admissions are a better
artifact than four of which one — `hullLemma44FamilyInclusionJoint` itself — was
unreachable by construction.  See the header of
`GGT/HullSCLemma44QuasiGeodesicBridge.lean` for the full diagnosis, including
what is **not** established: `RelativeGreendlingerStatement` is over-strong, but
it is not refuted here or anywhere in this repository.

**Counting `sorry`s says nothing about how far apart they are.**  Of the five,
`kotowskiOllivier` is a citation of a published construction;
`relativeIsoperimetricBridgeQuasiGeodesic` is a section of Osin's paper;
`estimatingSelectionConstruction` and `estimatingUnboundOutput` are two
propositions of his appendix, the second of them at the scale his argument
supplies; and `hullRelatorRespelling` is combinatorial, with its joint half
already the theorem `HullSC.jointRelatorRespellingStatement_proved`.  A count
treats those as five of one thing.  They are not.

## No admission here stands for a refuted statement any more

Until `c685697b9` one of them did.  `estimatingUnboundOutput` was stated at the
universal unbound-budget form, which
`Estimating/UnboundSmallMuCounterexample.not_estimatingUnboundOutputStatement`
and `Estimating/UnboundConjugateCounterexample`'s twin disprove independently at
the same universes, so the environment contained
`not_estimatingUnboundOutputStatement estimatingUnboundOutput : False` modulo
`sorryAx` and the hole could never be filled at its type.  That form is now
named `EstimatingUnboundOutputHistoricalStatement`, `EstimatingUnboundOutputStatement`
denotes the repaired statement carrying `UnboundEstimate.OsinUnboundScale`, and
the refutations follow the old name.  Every `¬ Estimating…` on `origin/main`
names the historical form or `EstimatingUnboundRepairedStatement`, an
intermediate; none names a statement admitted in this file.

So all five admissions below are now ordinary open debt.  That is a real change
in the state of Theorem C and it was not made here — it was made by the commit
that gave the unbound estimate Osin's scale.  This header said otherwise until
this commit, which rewrites these paragraphs and would have been restating a
false claim.

## The five `sorry`s must stay literal `sorry` tokens

This is the only file in the corpus with `sorry`s, and they carry more weight
than ordinary debt: all five reach both printed endpoints.

**Do not convert any of these to an unsolved goal, and do not `set_option
maxHeartbeats` or otherwise coax a tactic into "closing" one.**  An unsolved
goal is discharged by `sorryAx` with **no literal token in the source**, which
both the landing gate's lexical scan and a `grep` for `sorry` are blind to; a
refuted claim would then be held behind a gate that cannot see it.  The literal
token is the only thing keeping this file honest.

## What "the corpus has five `sorry`s and is otherwise clean" understates

That sentence is true and its significance is not what it sounds like.  This
module is reachable from the root (`GroupApproximation.lean`), and
`MFRecognition.SeedFromTheoremC` defines the paper's group `E` by `.choose` from
`manuscriptTorsionFreeFullMFRadical_openAdmissions`.  So the five holes are
load-bearing for a second lane, and counting them alongside ordinary open lemmas
misreports the state of the development — see the paragraph above on how far
apart they are.

Since 2026-09-07 every admission and both endpoints carry `#print axioms` lines
of their own, so a probe of this file **reports `sorryAx` on them** instead of
reporting nothing.  Before that the file emitted axiom lines only for four
clean leaves, so any per-file check saw those, found no `sorryAx`, and passed the
file: a report on part of the evidence read as a report on all of it.

**And the number of reports is still not the number of declarations affected.**
This module has far more declarations than it has `#print axioms` lines, and
everything downstream of the five admissions carries `sorryAx` too —
`hullLemma44FamilyInclusionJoint`, `hullLemma44FamilyInclusion`, `hullTheorem71`,
`hullInputs`, `literatureInputs`, both endpoints, and more.  Those emit nothing,
so no probe can see them.  Nothing is wrong: they are downstream of documented
admissions and that is what downstream means.  But the eight names a probe
prints are a fact about the reporters, not about the file.  The honest invariant
is not a count: it is **exactly five literal `sorry` tokens, and every
`sorryAx`-carrying declaration downstream of them.**

The directive has to be `#print axioms` and not `#audit_axioms`.  Both
`#audit_axioms` and `#audit_closed_axioms` are **gates, not reporters**: they
reject any declaration whose axioms fall outside `propext`, `Classical.choice`
and `Quot.sound`, so either one on a `sorry`-backed declaration is a build
error, not a report.  `#print axioms` emits the same line as an informational
message and lets the build proceed, which is what a file carrying deliberate
debt needs.  Do not "upgrade" these to `#audit_axioms`: the file will stop
building, and the honest report will be lost rather than strengthened.

Three gates would flag this and none of them bites today:
`scripts/TheoremCCompletionAudit.lean` applies `#audit_closed_axioms` to both
endpoints but is not a `lake` root and is not run by CI; the source-side
`scripts/check_non_mf_unconditional.py` rejects `sorry` only under `--strict`,
which CI does not pass; and that CI step is `continue-on-error: true`.

## The Chiodo field is no longer one of them

`ChiodoOfHigman.chiodo_of_omega` proves Chiodo's Theorem 3.10 from Higman's
ω-closure, so the first field of `LiteratureInputs` is discharged down to the
single construction `Higman.Omega.OmegaInput`.  That construction is proved, in
`Higman.OmegaFillLeadLinkBenign`, and read once for the whole repository from
`Higman.OmegaSharedProof`, which the recognition lane imports as well: one
theorem, shared by the two lanes that stand on it.

## Remaining proof implementations

* `kotowskiOllivier` — the density model at a parameter between `1/3` and
  `1/2`.  `Hyperbolic.SharpExistence` asks for an *infinite* finitely presented
  torsion-free hyperbolic group with property (T); every clause but property
  (T) is met by `Multiplicative ℤ`, and
  `Hyperbolic.CharTwoTorsionObstruction` records why no group this repository
  builds meets that one.
* `smallCancellationQuotient` — **proved** from the three Hull leaves.  Osin's
  Theorem 2.4 at the relatively hyperbolic pair `(U * H₀, U)` is Hull's
  one-step small cancellation over the free product
  (`GGT/RelHypOsin24FromHull.lean`, `GGT/RelHypProp23FromHullOsin24.lean`):
  one tied relator per prescribed element, iterated over the finite target
  set, with finite normal generation of the kernel a theorem of the
  construction (`GGT/RelHypOsin24Construction.lean`), torsion lifted through
  Lemma 4.9's correction, and suitability of the image from the preserved
  elementary closures.  Relative hyperbolicity is the labelled finite-base
  form of `GGT/RelHypDefinition.lean`; the earlier endpoint-only form admitted
  a duplicated peripheral and is refuted there.
* `osinTheorem12` — **proved**.  `minasyanOsin` is no longer a citation of its
  own: `E` acts on the Bass–Serre tree of its second HNN splitting
  (`GGT.BassSerreHNN`), `u₂u₁⁻¹` is loxodromic on it with the WPD property
  (`GGT/TreeWPDAxis.lean`), `E` is never virtually cyclic, and Osin's
  Theorem 1.2 `(AH₃) ⇒ (AH₁)` is
  `GGT.Elementary.osinTheorem12_unconditional`: Dahmani–Guirardel–Osin's
  Theorem 6.8 through their Theorem 4.42, whose proof is the
  Bestvina–Bromberg–Fujiwara projection complex (`GGT/DGOTheorem442*.lean`:
  the perturbed projections, standard paths, guards and barriers,
  hyperbolicity of the projection graph, the near-minimal double-coset
  relative generators, and inequality (41)).
* `hullCommonQuotient` — Hull's Corollary 7.4, which is Hull's Theorem 7.1
  applied to the free product of `E` with `H₀`, so it rests on the same four
  leaves as `hullTheorem71` does, together with the free product input;
  `HullSCCommonQuotientCorrected.hullCommonQuotient_of_oneStep_corrected` is
  that reduction, and `HullSC.FreeProductStatementCorrected` is the extra
  input.  The uncorrected `HullSC.FreeProductStatement` is **refuted**
  (`HullSCCommonQuotientCorrected.not_freeProductStatement`): it omits the
  non-elementarity of `H₀`, which `HullCommonQuotientStatement` supplies twice
  over.
* `hullLemma44FamilyInclusion`, `hullLemma49KernelPower` — the source-faithful
  quotient leaves.  Lemma 4.4 is
  recorded as injectivity of the natural quotient on the requested ball
  and joint preservation of the simultaneously selected peripheral family
  and of any original hyperbolically embedded family inside the alphabet,
  which is Hull's printed form and what Osin's Theorem 2.4 consumes; the
  selected-family form `hullLemma44Canonical` is its special case.  Lemma
  4.9 is recorded as its quotient-free kernel-power correction, exactly
  equivalent to order-preserving finite-order lifts.  Neither lemma is
  attributed a cone-off, rotating family, apex separation, or DGO conclusion.
  `HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49`
  assembles their literal quotient `G ⧸ normalClosure {w}`.  Hull's §6
  relator is transported into that same selected auxiliary family in
  `HullSCAuxiliaryRelatorPublished`, so the quotient and relator use one
  relative generating set.
* `hullTheorem71`, `osinLemma71` — the two fields of
  `HullCorrectedInputs.HullInputsCorrected`, both of them now proved.  They
  replace the four fields of
  `TorsionFree.HullInputs`, which cannot all be discharged: the kernel field of
  that structure quantifies over every `HullQuotient`, and at `m = 0` it asserts
  that the printed clauses alone force `q` to be injective, which the first
  projection `Q × Q → Q` of an acylindrically hyperbolic `Q` refutes
  (`HullFillKernelRefutation.not_kerNormallyGeneratedStatement`).  The remark on
  the kernel is a property of Hull's construction, so it travels with the
  quotient as a field of `HullCorrectedInputs.HullQuotientNG`; and Hull's
  Corollary 5.7 with Lemma 5.8 is not a citation at all over a torsion-free
  ambient group
  (`Manuscript.NonMF.HullInputsProved.exists_pair_suitable_of_torsionFree`),
  which is the only case `lem:saturation` uses.  So Hull's four cited results
  are two.
* `relativeIsoperimetricBridgeQuasiGeodesic`, `hullRelatorRespelling` — the two
  admissions that replaced `hullLemma44FamilyInclusionJoint`.  The first is
  Osin's Lemma 5.1 keeping its own `(1/2,0)`-quasi-geodesic case split, so that
  the certificate it consumes is the one Osin's Lemma 4.4 actually proves rather
  than the boundary-free form this repository had been demanding;
  `GGT/HullSCLemma44QuasiGeodesicBridge.lean` carries the diagnosis, the proof
  that narrowing the hypothesis strengthens the statement, and two findings that
  belong on the record — the `mu` range on which the certificate conclusion is
  free, and what is **not** established about
  `HullSC.RelativeGreendlingerStatement`.  The second is Hull's §6 re-spelling,
  whose joint half is already the theorem
  `HullSC.jointRelatorRespellingStatement_proved` and whose residue is
  `HullSC.OriginalRelatorRespellingStatement`.
-/

set_option warningAsError false

namespace GroupApproximation
namespace Manuscript
namespace NonMF

namespace TorsionFree

open GroupApproximation.HullGeometry

/-! ## Hull's small cancellation theorem and its companion -/

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

/-- **Open proof.**  Dahmani–Guirardel–Osin, *Hyperbolically embedded
subgroups and rotating families*, Theorem 5.3(b): for a separated very rotating
family on a hyperbolic geodesic space, every nonidentity element of the subgroup
the rotations generate is conjugate into a rotation subgroup or is loxodromic.

Three findings put the remaining proof boundary in this shape.

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

/-- **Open input.**  Osin's Lemma 6.5(a) selection: an `O`-equivalent
reduced diagram with a finite Definition-`M` scaffold whose estimating graph
satisfies the hereditary certificates, together with the choice of `rho`
against `mu` (`GGT/VanKampen/Estimating/Assembly.lean`). -/
theorem estimatingSelectionConstruction :
    GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0} := by
  sorry

/-! Reports `sorryAx`, which is the truth about this declaration. -/

#print axioms GroupApproximation.Manuscript.NonMF.TorsionFree.estimatingSelectionConstruction

/-- **Open input, and no longer a refuted one.**  Osin's unbound estimate at a
scale his argument supplies: `EstimatingUnboundOutputStatement` carries
`UnboundEstimate.OsinUnboundScale` as a hypothesis.

Until `c685697b9` this name denoted the universal unbound-budget statement,
which omits the scale assumptions and is refuted twice over.  That statement is
now `EstimatingUnboundOutputHistoricalStatement`, and it is what
`Estimating/UnboundSmallMuCounterexample.not_estimatingUnboundOutputStatement`
and `Estimating/UnboundConjugateCounterexample`'s twin disprove;
`EstimatingUnboundRepairedStatement`, an intermediate repair, is refuted there
as well.  **Neither refutation reaches the statement this declaration admits.**
Checked by enumerating every `¬ Estimating…` on `origin/main`: all three hits
name the historical or the intermediate form, none names this one.  See issue
#198. -/
theorem estimatingUnboundOutput :
    GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0} := by
  sorry

/-! Reports `sorryAx`, which is the truth about this declaration. -/

#print axioms GroupApproximation.Manuscript.NonMF.TorsionFree.estimatingUnboundOutput

/-- **Open proof.**  Osin, *Small cancellations over relatively hyperbolic
groups and embedding theorems*, arXiv:math/0411039v3, Lemma 5.1: the quotient
by a small cancellation family is again relatively hyperbolic over the image
peripheral family, in the two clauses the quotient consumer uses — a four-point
constant for the image relative alphabet, and a uniform pullback bound making
every quotient relative ball finite.

**The certificate hypothesis is Osin's, not the repository's.**  Until now this
input was stated with certificates demanded at *every* reduced diagram, which
only `HullSC.RelativeGreendlingerStatement` can supply, and that statement drops
the `(lambda,c)`-quasi-geodesic boundary its own source requires.  Osin does not
need certificates there: the proof of Lemma 5.1 begins "Suppose first that `p`
is not `(1/2,0)`-quasi-geodesic", decomposes the word in that branch, and only
then applies Lemma 4.4.  That case split belongs to Lemma 5.1, so it is inside
this statement now, and the certificate is asked only at diagrams with a
quasi-geodesic spelling.  The narrowing makes the hypothesis weaker and the
statement **stronger**, which
`HullSC.relativeIsoperimetricBridgeStatement_of_quasiGeodesicBridge` proves by
deriving the old form from this one; see the header of
`GGT/HullSCLemma44QuasiGeodesicBridge.lean`.

The neighbouring refutation does not reach it: `not_relativeLinearAreaTransferStatement`
kills the unbounded area transfer with a grid quotient whose relators are short,
and `RelWord.IsLemma44Input.long` excludes that family. -/
theorem relativeIsoperimetricBridgeQuasiGeodesic :
    HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0} := by
  sorry

/-! Reports `sorryAx`, which is the truth about this declaration. -/

#print axioms GroupApproximation.Manuscript.NonMF.TorsionFree.relativeIsoperimetricBridgeQuasiGeodesic

/-- **Open input.**  Hull's §6 relator family, presented over the selected
auxiliary alphabet, re-spells over the original peripheral family and over the
source joint family with the same normal closure and again a Lemma 4.4 input
above the prescribed thresholds
(`HullSC.HullRelatorRespellingStatement`).  It is combinatorial: no quotient, no
diagram certificate and no isoperimetric inequality occurs in it.

Half of it is already a theorem.  `HullSC.jointRelatorRespellingStatement_proved`
discharges the joint half by index relabelling, at unchanged parameters, but
under four structural hypotheses this statement does not carry — among them
`joint.base ⊆ selected.rel.base`, which
`HullSC.jointBase_subset_selectedBase_of_baseAdjoined` shows follows from the
family form's own binder as soon as the adjoined letters are asked to be base
letters rather than alphabet letters.  The residue proper is
`HullSC.OriginalRelatorRespellingStatement`, and its uniformity is where a
reader should look first: `eps` and `rho` are chosen before `W`, so it demands a
re-spelling for every small-cancellation family over the selected alphabet, not
for the one Hull constructs. -/
theorem hullRelatorRespelling : HullSC.HullRelatorRespellingStatement.{0, 0} := by
  sorry

/-! Reports `sorryAx`, which is the truth about this declaration. -/

#print axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullRelatorRespelling

/-- **Hull's Lemma 4.4 in its family form with the source joint family bound
explicitly** (`GGT/HullSCLemma44FamilyInclusionStatement.lean`); the previous
unbound form was over-strong, since at the identity quotient with the empty
relator family it produced the joint embedding for free
(`HullSC.jointAuxiliaryPeripheralEmbedding_of_familyInclusion`).

This is no longer an admission of its own.  It is assembled from the two
estimating admissions above, the two proved vk-side theorems, Osin's Lemma 5.1
at its own boundary hypothesis and the §6 re-spelling.  The relative
Greendlinger input is
`HullSC.RelativeGreendlingerQuasiGeodesicSpellingStatement`, which
`HullSC.relativeGreendlingerQuasiGeodesicSpellingStatement_of_components`
proves; the unrestricted `HullSC.RelativeGreendlingerStatement`, which is
stronger than Osin's Lemma 4.4 and which nothing in this repository can reach,
no longer appears anywhere above this line. -/
theorem hullLemma44FamilyInclusionJoint :
    HullSC.HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{0, 0} :=
  HullSC.hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_quasiGeodesicControls
    (HullSC.relativeGreendlingerQuasiGeodesicSpellingStatement_of_components
      estimatingSelectionConstruction
      GGT.VanKampen.estimatingPieceConstructionStatement
      estimatingUnboundOutput
      HullSC.relativeDiscRealizationSpellingStatement
      HullSC.relativeExteriorArcConversionAtWordRotatedStatement)
    relativeIsoperimetricBridgeQuasiGeodesic
    hullRelatorRespelling

/-! Reports `sorryAx`, inherited from the four admissions it is assembled from. -/

#print axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullLemma44FamilyInclusionJoint

/-- **Open proof.**  Hull, Lemma 4.4, in the form Hull prints it: the natural
quotient by a relator family satisfying the small cancellation condition is
injective on the requested Cayley ball and preserves both the simultaneously
selected auxiliary peripherals and any original hyperbolically embedded
family contained in the alphabet, jointly.  The family form is what
Fournier-Facio's Proposition 2.3 consumes through Osin's Theorem 2.4
(`GGT/RelHypProp23FromHullOsin24.lean`); the selected-family form used by
Theorem 7.1 is its special case.  No rotating-space geometry is attributed to
the lemma. -/
theorem hullLemma44FamilyInclusion :
    HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0} :=
  HullSC.hullLemma44CanonicalQuotientFamilyInclusionStatement_of_proposition414Uniform
    dgoProposition414Uniform hullLemma44FamilyInclusionJoint

/-- Hull's Lemma 4.4 for the selected family alone, the special case of the
family-inclusion form in which the original hyperbolically embedded family is
empty. -/
theorem hullLemma44Canonical :
    HullSC.HullLemma44CanonicalQuotientStatement.{0} :=
  HullSC.hullLemma44CanonicalQuotientStatement_of_familyInclusion
    hullLemma44FamilyInclusion

/-- Conversion of a planar exterior arc into the algebraic boundary
contiguity at a supplied word, retaining the source relator rotation.  The
fixed-relator predecessor is refuted by `ExteriorArcCounterexample`; the
rotated statement follows from the region's shelling and short sides. -/
theorem relativeExteriorArcConversionAtWord :
    HullSC.RelativeExteriorArcConversionAtWordRotatedStatement.{0, 0} :=
  HullSC.relativeExteriorArcConversionAtWordRotatedStatement

/-- Hull's Lemma 4.9 for a nontrivial power of a shortest representative,
from Osin's three estimating propositions (the piece construction is the
theorem `GGT.VanKampen.estimatingPieceConstructionStatement`, the realization
at a supplied spelling is the theorem
`HullSC.relativeDiscRealizationSpellingStatement`) and the arc-conversion
input above
(`GGT/HullSCLemma49PowerDiagramFromComponents.lean`). -/
theorem hullLemma49GeodesicPowerDiagram :
    HullSC.HullLemma49ShortestGeodesicPowerDiagramStatement.{0, 0} :=
  HullSC.hullLemma49ShortestGeodesicPowerDiagramStatement_of_estimating
    estimatingSelectionConstruction
    GGT.VanKampen.estimatingPieceConstructionStatement
    estimatingUnboundOutput relativeExteriorArcConversionAtWord

theorem hullLemma49KernelPower :
    HullSC.HullLemma49KernelPowerStatement.{0, 0} :=
  HullSC.hullLemma49KernelPowerStatement_of_geodesicPowerDiagram
    hullLemma49GeodesicPowerDiagram

/-- Hull's torsion-free canonical filling quotient, assembled directly from
Lemmas 4.4 and 4.9.  The quotient is literally the quotient by the normal
closure of the chosen relator; Lemma 5.8 supplies its alphabet and suitability
clauses. -/
theorem hullCanonicalQuotient :
    HullSC.TorsionFreeHullCanonicalQuotientStatement.{0} :=
  HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49
    (HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      hullYiSuitableFiniteFamily)
    hullLemma44Canonical hullLemma49KernelPower

/-- **Hull's Theorem 7.1 at `m = 1`.**  The target is adjoined to the base
before Lemmas 4.4 and 4.9 choose their constants.  Hull's exact §6 relator is
then transported from its focused pair into the complete selected auxiliary
family, preserving every published `C₁` clause.  Thus the relator and the
canonical quotient use literally the same relative generating set: the
relation `t⁻¹u` gives `q(t) = q(u) ∈ q(N)`, and the canonical kernel is its
normal closure. -/
theorem hullOneStep : HullSC.HullOneStepStatement.{0} :=
  HullSC.AuxiliaryPeripheralFamily.hullOneStep_of_canonicalQuotient
    hullCanonicalQuotient

/-- **Hull, *Small cancellation in acylindrically hyperbolic groups*, Theorem
7.1**, in the finite-set formulation the manuscript records, together with the
manuscript's remark on his construction: the kernel of `q` is normally
generated by `m` elements.  The remark is a field of the quotient
(`HullCorrectedInputs.HullQuotientNG`) because it is a property of the
construction rather than of an arbitrary quotient with the printed properties.

**No longer a citation of its own.**  Everything between the four leaves above
and this statement is proved in `GGT/HullSC*.lean`:

* `hullOneStep` above — Hull's §6 relator fed to his Theorem 5.1 over the pair,
  and then the two clauses that mention the target `t`.
* `HullSC.hullBallFormNG_of_oneStep` — the induction on `m`, whose kernel
  arithmetic is `HullSC.ker_comp_eq` and whose radius bookkeeping is
  `HullSC.image_cayleyBall_subset`: the balls of `Γ(G,A)` are infinite when `A`
  is, so the image of the `R`-ball has to be shown to sit in the `R`-ball of the
  quotient at the *same* radius rather than swallowed by a larger one.
* `HullCorrectedInputs.smallCancellation_of_ballFormNG` — the published
  injectivity-radius form turned into the finite-set form. -/
theorem hullTheorem71 :
    ∀ {G : Type} [Group G] [IsAcylindricallyHyperbolic G]
      (_hG : IsPowerTorsionFree G) (A : HullGeneratingSet G) {N : Subgroup G},
        Suitable A.alphabet N →
        ∀ {m : ℕ} (t : Fin m → G) {F : Set G}, F.Finite →
          Nonempty (HullCorrectedInputs.HullQuotientNG N t F) := by
  intro G _ _ hG A N hN m t F hF
  exact HullCorrectedInputs.smallCancellation_of_ballFormNG
    (HullSC.hullBallFormNG_of_oneStep hullOneStep) hG A hN t hF

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

/-- Hull's inputs, as a term: the two theorems above, and nothing else.  Hull's
Corollary 5.7 with Lemma 5.8 is not a field of the corrected bundle — over a
torsion-free ambient group it is
`Manuscript.NonMF.HullInputsProved.exists_pair_suitable_of_torsionFree`, and
that is the only case `lem:saturation` uses. -/
def hullInputs : HullCorrectedInputs.HullInputsCorrected.{0} where
  smallCancellation := hullTheorem71
  osinNonElementary := osinLemma71

end TorsionFree

namespace TheoremC

/-! ## Chiodo's Theorem 3.10, reduced to Higman's ω-closure -/

/-- **Chiodo, Theorem 3.10 (= Belegradek, Theorem A.1)**, on the ω-closure
rather than on a citation of its own: `chiodo_of_omega` proves it outright from
Higman's ω-closure, and the ω-closure is `Higman.OmegaSharedProof.omegaInput`, the
repository's single record of that construction. -/
theorem chiodo : ChiodoBelegradek.Statement :=
  chiodo_of_omega Higman.OmegaSharedProof.omegaInput

/-! ## The four citations of Fournier-Facio's paragraph that remain -/

/-- **Open proof.**  Kotowski–Kotowski and Ollivier–Wise: the density
model at a parameter between `1/3` and `1/2` gives an infinite finitely
presented torsion-free hyperbolic group with property (T). -/
theorem kotowskiOllivier : KotowskiOllivierStatement := by
  sorry

/-! Reports `sorryAx`, which is the truth about this declaration. -/

#print axioms GroupApproximation.Manuscript.NonMF.TheoremC.kotowskiOllivier

/-- **Fournier-Facio et al., Proposition 2.3, no longer a citation of its
own.**  Osin's Theorem 2.4 at the relatively hyperbolic pair `(U * H₀, U)` is
Hull's one-step small cancellation over the free product
(`GGT/RelHypOsin24FromHull.lean`, `GGT/RelHypProp23FromHullOsin24.lean`): the
tied one-relator quotients are iterated over the finite target set, finite
normal generation of the kernel is a theorem of that construction
(`GGT/RelHypOsin24Construction.lean`), torsion lifts through Hull's Lemma 4.9
correction, and suitability of the image follows from the preserved
elementary closures.  The three geometric leaves are the ones Theorem 7.1
already rests on: Lemma 4.4 in its family form, Lemma 4.9, and the Yi pair. -/
theorem smallCancellationQuotient : FournierFacioQuotientStatement :=
  GGT.RelHyp.fournierFacioQuotientStatement_of_hull_osin24
    TorsionFree.hullLemma44FamilyInclusion TorsionFree.hullLemma49KernelPower
    TorsionFree.hullYiSuitablePairAvoidingFiniteOneSided

/-- **Open proof.**  Osin, *Acylindrically hyperbolic groups*, Theorem
1.2, in the implication `(AH₃) ⇒ (AH₁)`: a group that is not virtually cyclic
and acts on a hyperbolic space with a loxodromic WPD element is acylindrically
hyperbolic.  This is the theorem Minasyan–Osin cite as their Theorem 3.3, and
after `GGT/TreeWPDAxis.lean` it is all that is left of their tree criterion at
`E`.  `GGT.osinTheorem12_of` splits it into Dahmani–Guirardel–Osin's Theorem
6.8 and Osin's `(AH₄) ⇒ (AH₁)`. -/
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

/-- **Hull, *Small cancellation in acylindrically hyperbolic groups*,
Corollary 7.4**: his Theorem 7.1 in one-step form
(`TorsionFree.hullOneStep`, on that section's four §5/§6 leaves over a pair)
applied twice over the free product, with the union-alphabet geometry the only
further input. -/
theorem hullCommonQuotient : HullCommonQuotientStatement :=
  HullSC.hullCommonQuotient_of_oneStep_of_geometry TorsionFree.hullOneStep
    hullFreeProductUnionGeometry

/-- The cited inputs, assembled from the declarations above. -/
theorem literatureInputs : LiteratureInputs :=
  { chiodo := chiodo
    kotowskiOllivier := kotowskiOllivier
    smallCancellationQuotient := smallCancellationQuotient
    minasyanOsin := minasyanOsin
    hullCommonQuotient := hullCommonQuotient }

/-! ## Theorem C, assembled over five open admissions -/

/-- **Theorem C (`thm:torsion-free`), in radical form, assembled — NOT closed.**

The suffix is `_openAdmissions` and not `_closed` because this declaration
depends, through `literatureInputs` and `TorsionFree.hullInputs`, on all five of
this file's `sorry`s: `estimatingSelectionConstruction`,
`estimatingUnboundOutput`, `relativeIsoperimetricBridgeQuasiGeodesic`,
`hullRelatorRespelling` and `kotowskiOllivier`.
`hullLemma44FamilyInclusionJoint` is no longer among them — it is assembled from
the first four — but it still reports `sorryAx`, because they do.  It was named
`_closed` until 2026-09-07, and
`MFRecognition.SeedFromTheoremC` reads it by name to define the paper's `E`, so
the old name asserted to every reader and every by-name audit that Theorem C was
proved when it is not.

Since `c685697b9` no admission it rests on stands for a refuted statement, so
unlike its earlier state this declaration is not closed off in principle — only
open.  See this module's header. -/
theorem manuscriptTorsionFreeFullMFRadical_openAdmissions : PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical literatureInputs TorsionFree.hullInputs

/-- **Theorem C, in the simplified printed statement, assembled — NOT closed.**
Same five open admissions as the radical form, reached by the same two input
bundles. -/
theorem manuscriptTorsionFreeSimplified_openAdmissions : PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified literatureInputs TorsionFree.hullInputs

/-! **The two endpoints report `sorryAx`.**  They are not closed; see the module
header.  These lines exist so that the file reports on the declarations that
matter rather than only on its four clean leaves. -/

#print axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_openAdmissions
#print axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_openAdmissions

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
