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

### `STW/` and root-level `STWProblems.lean`: never compiled, and does not compile -- corrected finding

**Correction to the first version of this section.** It called the tree
"genuine, sorry-free operator-algebra infrastructure" and flagged it as
"worth a decision (superseded ... or a live parallel effort)." The lead built
all three `STW/Actual/*.lean` files by hand and it is neither: it does not
compile, in three different ways, and the mechanism is structural rather than
incidental. `sorry`-free was never in question and was never the relevant
property -- *compiling* is, and this tree has never had a compiler's opinion
of it, because nothing has ever built it. Its content has only ever been
checked by eye, by whoever wrote it and by this lane reading it afterward.
Record the finding as: **never compiled, and when compiled, broken.**

Build evidence, `lake env lean <file>` against the project environment, one
file at a time:

    STW/Actual/Flow.lean         EXIT=0, but 2 warnings:
                                  Overlapping instance parameters in `instCoe`
                                  (line 30) and `coe_mk` (line 32) --
                                  `[Ring A]` and `[One A]` infer conflicting
                                  `[One A]` -- an instance diamond, not lint noise
    STW/Actual/FockPair.lean     2 real proof errors:
                                  `simp` made no progress (line 135)
                                  `change` tactic failed, pattern mismatch (161)
    STW/Actual/CuntzCalkin.lean  error: unknown module prefix 'STW' (line 1)

Three different kinds of broken, and the third names the exact mechanism
this whole finding turns on. `CuntzCalkin.lean`'s first line is
`import STW.Actual.FockPair` -- a **sibling** import, inside the same
directory -- and it fails because `STW` resolves to nothing: with no
`lean_lib` entry naming it in `lakefile.toml`, there is no module prefix for
Lean to resolve `STW.*` against, even when compiling one file of the tree
against another by hand. **A file outside every lakefile target is not
merely unbuilt -- it is exempt from the lib's flags (which is why `Flow.lean`
passes today: `-DwarningAsError=true` never reaches it), and it cannot even
reference its own siblings by import.** That second half is the sharper
statement of the original finding: this is not "orphaned, could be wired,"
it is a tree that cannot resolve its own internal imports without a lakefile
entry first, so nobody has ever been able to build more than one file of it
in isolation, let alone the whole thing against the corpus.

**Decision, made rather than left open:** not a live parallel effort to wire,
and not a supersession in the `AlgTop`->`CharClass` sense lix-orphans found
elsewhere in this same hunt -- a superseded route at least worked once. This
is abandoned work that stopped being checked the moment it left the build,
if it was ever checked at all. Nobody should wire it as landed; if Problem LV
is attempted in Lean, this tree is a source of ideas (the Fock-space Cuntz
model, the KMS uniqueness argument), not of theorems -- every claim in it
needs reproving against a compiler, not merely re-reading.

### Why no lakefile target found it, and why intent does not equal correctness

`lakefile.toml`'s `lean_lib` entries are exactly `GroupApproximation`,
`Audit`, `PalomarChallenge`, `PalomarSolution`. Neither `STW` nor
`STWProblems` is one of them, and no file under `GroupApproximation/` imports
`STW.*` (`git grep '^import STW'` over the tree: empty). This is a different
kind of defect from an ordinary orphan, not merely a bigger one:
`lix-orphans`' 101 orphans at least sit inside the `GroupApproximation` lib,
which globs its whole directory, so `lake build` compiles them regardless of
import wiring, and a compiler has an opinion about every one of them. `STW/`
and `STWProblems.lean` (~600 lines total) are outside every target `lake
build` knows about, outside the scope of a directory-walk sweep confined to
`GroupApproximation/`, and -- now confirmed -- outside the reach of a
compiler altogether until built by hand.

Read in full before the build result came back: superficially genuine
operator-algebra content, its own docstring explicit that it builds "the
actual operator-algebra objects used by Problems XXII, LV, and XCV" rather
than abstract stand-ins -- concrete Fock-space prefix-shift isometries meant
to satisfy the Cuntz relations (`STW/Actual/FockPair.lean`, toward Problem
LV's O2 model), KMS-equation uniqueness lemmas (`STW/Actual/Flow.lean`, also
LV), and a re-export of the XCV compact-`K_0` obstruction
(`STWProblems.lean`'s `ProblemXCV` namespace). That reading was accurate
about intent and wrong about status, which is exactly the lesson: a `sorry`-
free lexical scan and a careful read are both blind to a failed tactic, and
neither can see an import that cannot resolve. It does not complete an
advertised endpoint either way -- Problem LV has no Lean endpoint anywhere in
this repository (Cairn's `stw99-problem-lv-quasifree-flows-o2` is established
by a paper route only), and Problem XXII's actual wired route
(`Analysis/STW22*`) never imports or needs this tree -- so this was never a
second XXII regardless of the build result. It is, now confirmed rather than
inferred, abandoned and unverified work that two independent sweeps today
(`lix-orphans`' directory walk, this one) each missed for a different reason.

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

## Addendum: the rest of the `*Input` list, checked

Completed the sweep of every remaining `*Input`-named `: Prop` structure/def
found by the same grep, at the lead's request. Read at `origin/main`
`24db72a029e8516e7cd1334d8e67d56d85445029`. Method for each: grep every file
that mentions the name for a zero-remaining-hypothesis term of the exact
type, then read context rather than trust the keyword. Two looked like
discharges and were not; the rest showed no discharge signal at all
(confirmed by grepping for `theorem`/`def <name> : <Input>` with no leading
binder across the whole tree -- zero hits for every name below except the two
discussed).

* **`SkeletonAH3Input`** (`GGT/WPDMinasyanOsinSkeleton.lean`) --
  **discharged and already wired, not a gap.** `GGT.TreeWPDAxis`'s
  `skeletonAH3Input_unconditional : SkeletonAH3Input.{0}` is a genuine
  zero-hypothesis proof, consumed by `minasyanOsinStatement_of` in the same
  file, whose result feeds `GGT.BassSerreDoubleHNN.minasyanOsinStatement_of_osinTheorem12`,
  which `Manuscript/NonMF/TheoremCAssembly.lean:480-491` applies directly to
  `osinTheorem12 : GGT.OsinTheorem12` in the manuscript's own Theorem C
  assembly. All of `WPDMinasyanOsinSkeleton`, `TreeWPDAxis`,
  `BassSerreDoubleHNN`, `BassSerreHNNAxisWPD` are wired
  (`GroupApproximation.lean:2317,2320,2321,2388`). Fully connected end to end;
  the file's own docstring even warns against recording it as debt.
* **`CactusBoundaryInput`, `StarLayerConstructionCertificateInput`**
  (`GGT/KazhdanHypGirthEightBuild.lean`) -- the `(T := emptyTriangleTableBuild)`
  instances that looked like discharges are the corpus's own
  `*ModelTest`-style sanity checks at the trivial/`PEmpty` group (the
  standing order lix-orphans already documented for a different cluster:
  every hypothesis-bearing `Prop` gets a non-vacuous concrete instance), not
  proofs of the general statement. The one real reduction present,
  `cactusBoundaryInput_of_orientedCactusBoundaryProducer`, still carries a
  hypothesis (`OrientedCactusBoundaryProducer`) -- it moves the goalpost, it
  does not discharge it. Both remain genuinely open.
* **Every other name below**: no discharge signal of any kind found --
  `AmenableMFInput`, `WinterZachariasInput`, `CoronaOrderZeroLiftInput`,
  `AmenableUCTInput`, `TikuisisWhiteWinterCoreInput`, `CoronaEmbeddingInput`,
  `RosenbergSchochetInput`, `DadarlatEilersInput`, `OmegaTowerInput`,
  `HalfLineInput`, `RightTailASubInput`, `BlackadarKirchbergNFConverseInput`,
  `OperativePureInfinitenessInput`, `FreeGroupPFFBaseInput`. Where a name
  reappears in several "Derivation"/"Proof"-suffixed files (e.g.
  `AmenableUCTInput` in six), that is the expected shape of a genuinely open
  hypothesis threaded unchanged through a composition chain, not a sign of
  hidden progress -- confirmed for a sample of these by reading the actual
  binder lists, not just counting file hits.

`AmenableMFInput` (`Analysis/AmenableMFInput.lean`) deserves its own line:
its docstring is unusually explicit that it is a genuinely irreducible gap --
"the gap ... is not slack in the estimates; it is the whole of
Tikuisis--White--Winter" -- and separately explains a **tooling trap**
worth flagging on its own: a producer of this input stated from bare
`∀`-premises would enter the "discharge fixpoint" of
`scripts/check_non_mf_unconditional.py` and be silently marked inhabited by
that script even though nothing constructs it. That script is the mechanism
this whole hunt is a manual stand-in for, on this corpus; if a second XXII
exists via *that* particular failure mode rather than an orphan import, this
script's own discharge-fixpoint logic is where to look, not another grep pass
over `*Input` names. Flagging for whoever owns `check_non_mf_unconditional.py`
rather than chasing it further here, since it is a claim about a script's
behaviour, not about this corpus's mathematics.

## Still open: directories not swept by name at all

Not checked by this pass, beyond the `*Input`-name grep above (structure/def
name, declaring file, for completeness of the original list):

Every `*Input`-named `structure`/`def : Prop` the original grep found is now
checked (addendum above); none remain from that list. Excluded from the
pattern on inspection, not overlooked: `StabilizationInput`, `SumBoundInput`,
`QuasiSumBoundInput`, `AuxiliaryCyclePathInput`, `TwoHalfPathInput`,
`FreeProductInput`, `IsBoundedLemma44Input`, `OmegaInput`, `RandomGroupInput`,
`LatticeRouteInput`, `SpectralRouteInput`, `TarskiInput`, `RopeInput` are all
data-bundling structures (route/certificate parameters, not `Prop`), confirmed
by reading their declarations directly -- the `*Input` naming convention is
not exclusive to unproved-literature-citation hypotheses, and grepping the
name alone overcounts unless each hit is read.

Directories not swept by any method in this report: `Leavitt/`, most of
`Higman/` (beyond the two `*Input` names above and their neighbours),
`Computability/` (beyond `FreeGroupPFFBaseInput`'s file), the GGT
small-cancellation corpus beyond the files the `*Input` and docstring-pattern
greps surfaced, and `.md` files under `notes/` (the docstring-pattern grep
covered `GroupApproximation/**/*.lean` only). A `*Input`-name grep is
necessarily blind to a genuinely open hypothesis that carries no such suffix;
these directories have not been checked by any method that would catch one.
