# Strengthening-hunt sweep, 2026-09-07

Lane `lix-meta`. Task, following `lix-orphans`' discovery that
`STW22AntipodalFactorialPair.lean` proves the "missing conjunct" of the XXII
endpoint: find every other instance in this repository of a result that is
proved and landed, and that would strengthen or complete a statement the
repository already advertises. Read at `origin/main`
`c89d15720347b3aa1bb0d8d7d41ef09e28ebc98d` unless a narrower SHA is named.
Nothing in this file was wired, edited, or built by this lane; every "does it
compile" question below is explicitly left open where noted.

## Positive findings

### `STW/` and root-level `STWProblems.lean` are in no lakefile target at all

`lakefile.toml`'s `lean_lib` entries are exactly `GroupApproximation`,
`Audit`, `PalomarChallenge`, `PalomarSolution`. Neither `STW` nor
`STWProblems` is one of them, and no file under `GroupApproximation/` imports
`STW.*` (`git grep '^import STW'` over the tree: empty). This is a stronger
defect than an ordinary orphan: `lix-orphans`' 101 orphans at least sit inside
the `GroupApproximation` lib, which globs its whole directory, so `lake build`
compiles them regardless of import wiring; `STW/Actual.lean`,
`STW/Actual/{Flow,FockPair,CuntzCalkin}.lean` and `STWProblems.lean` (~600
lines total) are outside every target `lake build` knows about, and outside
the scope of a directory-walk sweep confined to `GroupApproximation/`.

**The lead independently confirmed this is a live defect, not a hygiene
footnote.** No `.olean` for any `STW*` module exists anywhere in the build
clone -- this tree has never been compiled by any build in the repository's
history. Compiled by hand (`lake env lean STW/Actual/Flow.lean`): passes,
`EXIT=0`, but with two warnings (`STW/Actual/Flow.lean:30,32`, overlapping
instance parameters on `instCoe`/`coe_mk`, a genuine instance-diamond risk).
The `GroupApproximation` lib sets `moreLeanArgs =
["-DwarningAsError=true"]`, so this file compiles today only *because* it
sits outside that lib; wiring it into any warning-as-error target would turn
both warnings into hard build failures. The tree has been drifting below the
standard every other file in the corpus is held to, silently, because nothing
has ever checked it against that standard.

Content, read in full: genuine, sorry-free operator-algebra infrastructure,
its own docstring explicit that it builds "the actual operator-algebra
objects used by Problems XXII, LV, and XCV" rather than abstract stand-ins --
concrete Fock-space prefix-shift isometries satisfying the Cuntz relations
(`STW/Actual/FockPair.lean`, toward Problem LV's O2 model), KMS-equation
uniqueness lemmas (`STW/Actual/Flow.lean`, also LV), and a re-export of the
XCV compact-`K_0` obstruction (`STWProblems.lean`'s `ProblemXCV` namespace).
**It does not itself complete an advertised endpoint**: Problem LV has no
Lean endpoint anywhere in this repository (Cairn's
`stw99-problem-lv-quasifree-flows-o2` is established by a paper route only),
and Problem XXII's actual wired route (`Analysis/STW22*`) never imports or
needs this tree. So this is not a second XXII; it is real, sizeable work that
two independent sweeps today (`lix-orphans`' directory walk, this one) would
each have missed for a different reason, and it is now below the corpus's own
warning standard. The lead is building the remaining two files
(`STW/Actual/{FockPair,CuntzCalkin}.lean`) to check the same thing.

### The public XXII endpoint is `negativeSolutionToProblemXXII`, not only `antipodal_stw22_trace_problem_counterexample`

`lix-orphans` names `antipodal_stw22_trace_problem_counterexample`
(`Analysis/STW22UnconditionalCore.lean:49`) as the wired-but-weaker
conjunction. One file further downstream,
`Analysis/STW22NegativeSolution.lean`, imports it and states
`negativeSolutionToProblemXXII`, whose own docstring calls itself "the final
public endpoint" and says outright "there are no parameters or mathematical
hypotheses"; it too is `#audit_closed_axioms`-clean and lacks
`IsFactorialTraciallyCompletePair` among its nine conjuncts, for the same
reason. Corroborates `lix-orphans`' finding from one level further down the
dependency chain rather than adding a new gap; recorded so the eventual fix
also updates (or is cited alongside) this declaration, not only the one
`lix-orphans` named. **Independently corroborated by lane `xxii-fix` from a
different direction**, per the lead.

## Negative findings, with reasons (so nobody re-runs these searches)

### The Kazhdan-transport "not yet wired" docstring is stale, not a gap

`Sofic/LiteralRouteTransport.lean`'s docstring says the printed reverse-step
identity, formalized in `Analysis/PrintedReverseTransport.lean`, "had no
consumer" and "is not yet wired to the finite-stage reverse transport." True
when written; false now. `Sofic/PrintedReverseTransportRoute.lean` (landed,
wired at `GroupApproximation.lean`) is exactly that consumer --
`transport_star_printed`, `transport_both_printed`,
`compressionGroup_transport_both_printed`. This whole area (proof-ledger rows
`ID.04`--`ID.06`, `FN.03`) is tracked by
`metadata/NON_MF_NOTES_PROOF_LEDGER.md`, which already graded `ID.06` CLOSED
against a certified green `Build and audit` run (`dd1ca3546`, run
`32217510998`). The ledger process that governs this corpus already catches
exactly this failure mode; it is not a fruitful place to look for a second
XXII, because a mechanism already exists there to prevent one.

### Two compiling, unwired `lix-orphans` WIRE-bucket files don't fix a missing-conjunct gap

`Analysis/STW22CounterexampleCompactnessRoute.lean` proves `T(A) ⊊ T(M)` by a
second, Hahn--Banach/Jordan-decomposition route; its own docstring says it was
"restored ... kept because it is a genuinely different derivation of the same
conclusion, not because anything depends on it" -- an alternate citable proof
of a fact the wired route already establishes a different way, not a
completion of anything missing. `Analysis/STW22FibreEvaluation.lean` proves
`blockEval_surjective`, cited by "the STW Problem XXII audit" per its
docstring, but no reachable declaration anywhere in the corpus consumes it
(grepped `blockEval_surjective` and its neighbours: only inside this file).
Read for a "this is what X needs" claim in either docstring: neither makes
one.

### Two compiling, unwired GGT files: no strengthening claim found

`GGT/DGOProposition414SecondSeparationHalfWord.lean` and
`GGT/HullSCLemma44PrefixKernelCutConstruction.lean` (both confirmed compiling
by `lix-orphans`, both still unwired). Read both in full: internal
assembly/bookkeeping lemmas for a larger small-cancellation induction
(isolating a retained wrapped source in a half-word cut; assembling a
prefix-cone cut certificate from two independent one-step outputs). Neither
docstring, nor anything I could find citing either declaration name, claims
either completes a printed statement (DGO Lemma 4.21(b), Osin's Lemma 4.4, or
otherwise). `lix-orphans` explicitly flagged that it had not cross-checked
manuscript fidelity for this cluster; this pass does not find fidelity
significance either, but does not rule it out with the same confidence as the
STW22 pair above -- these two would need someone who owns the DGO/Hull-SC
induction to say whether the printed lemma needs them.

### `*Input`-named literature-citation hypotheses: two near-misses, both non-findings on the actual text

Systematic grep for `structure`/`def <Name>Input : Prop` across
`GroupApproximation/`, ~30 hits total (list below, in "still open" section).
The two whose surrounding text looked most like a hidden discharge, checked
in full:

* **`AmenableNuclearInput`** (Lance's nuclearity-from-amenability theorem,
  `Analysis/TikuisisWhiteWinter.lean:157`) genuinely *is* discharged --
  `Analysis/LanceNuclearAmenable.lean`'s `amenableNuclearInput : QuasidiagonalMF.AmenableNuclearInput`,
  zero hypotheses. But `Analysis/TikuisisWhiteWinterUnconditional.lean`
  explicitly restructured the whole route to no longer need it: "this wave
  removes from the route everything that is not the theorem itself," leaving
  exactly one un-discharged hypothesis, the raw quasidiagonal-trace fact
  (`QuasidiagonalMF.TikuisisWhiteWinterInput` stays, in the same file's own
  words, un-inhabited: "no declaration in this repository inhabits" it). So
  the Lance discharge is real but sits on a route the corpus has already
  abandoned in favour of a leaner one; it completes nothing on the live
  critical path.
* **`TikuisisWhiteWinterInput`** itself: the grep hit that looked like a
  discharge ("this repository inhabits `QuasidiagonalMF.TikuisisWhiteWinterInput`")
  is the tail of a *negated* sentence -- "no declaration in this repository
  inhabits" it, read in isolation from context by a bare grep. Read in
  context, it is the same file stating the gap, not closing it.

### Eleven `Manuscript/NinetyNineProblems/*.lean` files checked against their printed STW statements

`ProblemX.lean`, `ProblemXGroups.lean`, `ProblemXImpliesIX.lean`,
`ProblemXWitness.lean`, `ProblemXCliffordWitness.lean`,
`ProblemXCVCompactKTheory.lean`, `KazhdanQuasidiagonalTraces.lean`,
`FactorizationProperty.lean`, `FactorizationImpliesHyperlinear.lean`,
`FactorizationHyperlinearTheorem.lean`, `StablyFinite.lean`. All wired
(confirmed each import line present in `GroupApproximation.lean`). Each is
explicit in its own docstring about exactly what it does and does not assert
-- `StablyFinite.lean` states outright "Neither [problem] is asserted
anywhere below"; `ProblemX.lean` justifies its universe pin (`.{1}`) rather
than leaving it silent; `FactorizationImpliesHyperlinear.lean` names its own
open step precisely and `FactorizationHyperlinearTheorem.lean` records
closing it (`BrownAmenableTraceHyperlinearInput`, discharged and consumed --
"the citation becomes a theorem," two restatements given, old form kept
alongside per policy). No missing conjunct, no silently-dropped hypothesis,
no unjustified universe choice found in any of the eleven. (Problem LIX was
already handled this session; see
`notes/lix-lane-reports/lix-lemma-two-lean-closure-2026-09-07.md`.)

Also checked and confirmed genuinely open (not hidden): `KirchbergKazhdanFactorizationInput`,
`KirchbergKazhdanQuasidiagonalInput`, `ThomSoficKazhdanNonResiduallyFiniteInput`,
`TranslationCPAPReductionInput`, `NuclearImpliesAmenableInput` -- each explicitly
documented at its declaration site as "assumed," "no inhabitant," or "the
repository has neither X nor Y," and none has an unconnected discharge sitting
elsewhere (single-consumer, single-file for the last two; the others checked
by name across the whole tree).

## Still open: the rest of the `*Input` list, and untouched directories

Not yet checked in depth (structure/def name, declaring file):

* `AmenableMFInput` -- `Analysis/AmenableMFInput.lean`
* `StabilizationInput` -- `Analysis/CStarStabilization.lean`
* `DadarlatEilersInput` -- `Analysis/DadarlatEilers.lean`
* `WinterZachariasInput`, `CoronaOrderZeroLiftInput` -- `Analysis/KirchbergRordamOrderZeroLift.lean`
* `AmenableUCTInput` -- `Analysis/TikuisisWhiteWinter.lean`
* `TikuisisWhiteWinterCoreInput` -- `Analysis/TikuisisWhiteWinterCore.lean`
* `CoronaEmbeddingInput` -- `Analysis/TikuisisWhiteWinterDerivation.lean`
* `RosenbergSchochetInput` -- `Analysis/UniversalCoefficientTheorem.lean`
* `SumBoundInput`, `QuasiSumBoundInput`, `AuxiliaryCyclePathInput`,
  `TwoHalfPathInput` -- `GGT/DGOProposition414*.lean`
* `FreeProductInput` -- `GGT/HullSCCommonQuotient.lean`
* `IsBoundedLemma44Input` -- `GGT/HullSCLemma44BoundedInput.lean`
* `OmegaInput`, `OmegaTowerInput` -- `Higman/OmegaClosure.lean`, `Higman/OmegaTower.lean`
* `HalfLineInput` -- `Higman/OmegaHalfLineReduction.lean`
* `RightTailASubInput` -- `Higman/OmegaHalfLineSemanticGraphWitness.lean`
* `RandomGroupInput`, `LatticeRouteInput`, `SpectralRouteInput` -- `Kazhdan/SharpExistenceRoutes.lean`, `Kazhdan/SharpExistenceSpectralRoute.lean`
* `TarskiInput` -- `Manuscript/MFRecognition/PrintedTarskiCertificateSyntax.lean`
* `RopeInput` -- `Manuscript/MFRecognition/RopeObjects.lean`
* `BlackadarKirchbergNFConverseInput` -- `Manuscript/NonMF/PriorWorkBlackadarKirchberg.lean`
* `OperativePureInfinitenessInput` -- `Manuscript/OneSidedMFRadical/SentenceOperativePureInfinitenessClosure.lean`
* `CactusBoundaryInput`, `StarLayerConstructionCertificateInput` (two
  declaring files, `GGT/KazhdanHypGirthEightBuild.lean` and
  `GGT/KazhdanHypGirthEightStarProducer.lean` -- possible duplicate, not yet
  compared), `FreeGroupPFFBaseInput` -- `Computability/FreeEdgeTowerCode.lean`,
  `SkeletonAH3Input` -- `GGT/WPDMinasyanOsinSkeleton.lean`

Directories not swept at all: `Leavitt/`, `Computability/` (beyond the one
name above), most of `Higman/`, the GGT small-cancellation corpus beyond the
files named above, and `.md` files under `notes/` (the docstring-pattern grep
covered `GroupApproximation/**/*.lean` only).
