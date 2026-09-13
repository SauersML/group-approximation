# ROSTER — non-MF every-line unconditional swarm (launched 2026-09-13 ~01:10)

NM = /private/tmp/claude-501/-Users-user-nonsofic-existence/0a930a1d-0cf3-4aa0-b91a-b8bfce7d68c7/scratchpad/nm
Paths below are relative to `GroupApproximation/` unless they start with `metadata/`, `notes/` or `scripts/`.
Line numbers are from origin/main 31625a5f8; they drift, so grep the name.

## Walls: the four open binders of the top endpoints (`Manuscript/NonMF/TorsionFreeLiteratureInputsLeastArea.lean`)

| wall | Prop | producer route on main | lanes |
|---|---|---|---|
| hgreendlinger | `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}` (`GGT/VanKampen/Estimating/OsinAppendixSections.lean:120`) | `relativeGreendlingerQuasiGeodesicLeastArea_of_inputs o52LeastArea h94 hin` (`OsinAppendixAssembly.lean:134`). `o52LeastArea` is closed (`OsinAppendixO52LeastArea.lean:31`). h94 = `OsinLemma94SectionStatement` (`OsinAppendixSections.lean:303`). hin = `OsinSection97InputsStatement` = `MultipleEdgeCutInput ∧ LoopCutInput ∧ EulerCountInput ∧ DescentInput` (`OsinAppendixAssembly.lean:52`, `OsinAppendixSectionInduction.lean:75/85/96/120`). | hull-unbound, hull-count94, hull-select, go-lemma42, hull-euler, dgo-analytic, hull-respell |
| hbridge | `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0,0,0}` (`GGT/HullSCLemma51EmbeddedBridge.lean:110`) | from `QuotientPeripheralLetterPullbackStatement` (`GGT/HullSCLemma51EmbeddedProducer.lean:122`) | hull-bridge, hull-component |
| hKO | `TheoremC.KotowskiOllivierStatement` := `Hyperbolic.SharpExistence` (`Manuscript/NonMF/FournierFacioInput.lean:71`) | `isHyperbolicGroup_ghb7_of_zipFold hzip hfold` (`Kazhdan/GHBHyperbolicDiscCounts.lean:84`), then `kotowskiOllivierStatement_of_ghb7ConjHyp (cckwFiniteOrderConjugateIntoVertex_of_fixedCliqueTits hT6 cckwCosetComplex_simplyConnected cckwCosetComplex_connected) isHyperbolicGroup_ghb7` (`GHBSharpExistenceSystolic.lean`, `GHBLatticeRouteKazhdan.lean`, `CCKWTitsGHB.lean`). hzip = `Systolic.ZipSpurStatement CCKW.cosetComplex` (`GGT/SystolicDisc.lean:421`). hfold = `MirrorFoldStatement` (`GGT/SystolicDisc.lean:432`). hT6 = `CCKW.SystolicInvariantCliqueStatement` (`Kazhdan/GHBSharpExistence.lean:34`). Alternative: `isHyperbolicGroup_ghb7_of_discInputs hfill hfold hcount hsum`. | kh-torsion, fff-periodic, systolic-counts, kh-cckw, ko-closed |
| hW | `FinitelyPresentedInfiniteSimpleStatement` (`Manuscript/NonMF/FournierFacioParagraphFromSimpleFactor.lean:353`) | `finitelyPresentedInfiniteSimpleStatement_of_stabK (h47 : StabKFinitelyPresented qTwo)` (`GroupTheory/HydeLodha/QTwoFinitelyPresented.lean:25/68`); Hyde–Lodha Prop 4.7 and Lemma 4.6 | simple-group, hl-lemma46, fff-quotient, kh-ejz |

`manuscriptRegularNonMFAlgebra_of_hullLeaves` also takes hDGO and hGO. Both are closed on main (`simpleUniqueTraceAtHypEmbedded_closed`, `gerasimovaOsinTheorem11Printed`).

## Cross-lane protocol
- Name split inside a wall: the integrator named in the lane section below decides the exact piece Props in its first report. Pieces are stated as `def ...Statement : Prop` in a small landed module, so peers can consume them before they are proved.
- Wiring: after landing a closed module that a census row or endpoint needs, append one line `<GroupApproximation.Module> <lane> <sha>` to `$NM/wire-queue.txt`. Lane root-wire wires it. Never edit `GroupApproximation.lean` yourself.
- Baseline lines (`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`): lanes do not edit the baseline. When a finding is retired, say so in your census row note ("retires <kind> <decl>"); the census lane removes the line.
- A needed statement owned by another lane: ask the lead with SendMessage. Do not build it.

## hull-unbound  (clone nm-a)
- Predecessor report: `notes/nm-swarm/reports/hull-unbound.md`; also read `sec5-sentences.md` (OsinUnboundMerged) and `hull-respell.md`.
- Target: INTEGRATOR of h94. Land the closed `theorem osinLemma94Section_closed : GGT.VanKampen.OsinLemma94SectionStatement` (rename if a peer name exists).
  - Pieces: OsinLemma94RunInput and its counting reduction (owner hull-count94); OsinUnboundCaseTwo (PinchSplit.transportDistinguished) and OsinUnboundMerged (both yours).
  - Land the assembly over explicit piece Props first, then close your pieces.
- Next: help hull-respell close hgreendlinger.

## hull-count94  (clone nm-b)
- Predecessor: none by name. Read `hull-unbound.md` and commit 82ba54dfb ("Draft Osin Lemma 9.4 run input and its counting reduction").
- Target: OsinLemma94RunInput and its counting reduction, closed, at the Prop hull-unbound's assembly consumes.

## hull-select  (clone nm-c)
- Predecessor: `$NM/lanes/hull-select.files` (29 files in flight).
- Target: closed `MultipleEdgeCutInput` (`OsinAppendixSectionInduction.lean`, `OsinAppendixCutSections`).

## go-lemma42  (clone nm-d)
- Predecessor report: `go-lemma42.md`.
- Target: closed `LoopCutInput` (`OsinAppendixSectionInduction.lean`, `OsinAppendixCutSections`).

## hull-euler  (clone ggt-repair)
- Predecessor report: `hull-euler.md`.
- Target: closed `PhiPrimeCountInput` (`OsinAppendixEulerCount`), along Osin's Lemma 9.3 route. `eulerCountInput_of_phiPrimeCount` (cdd4b82df) turns it into the `EulerCountInput` used by `OsinSection97InputsStatement`. Section form: `OsinPhiPrimeCountSectionStatement` (`OsinAppendixGreendlingerPocketParts`).
- 09-13 swap: hull-euler owns PhiPrimeCountInput and dgo-analytic owns SectionPocketCutInput.

## dgo-analytic  (clone ejz-integral)
- Predecessor report: `dgo-analytic.md`.
- Target: a closed `DescentInput`, from `OsinDescentMergeInput` and `OsinDescentStepInput` (`OsinAppendixAssemblyDescent.lean:67/94`).
- Also: closed `SectionPocketCutInput` (`OsinAppendixDescentCut.lean:71`). Together with hull-euler's PhiPrimeCountInput, `osinDescentSection_of_pocketParts` (`OsinAppendixGreendlingerPocketParts`) gives the descent part.
- Split with hull-euler: hull-euler owns PhiPrimeCountInput.

## hull-respell  (clone orph-algtop)
- Predecessor report: `hull-respell.md`.
- Target: `theorem relativeGreendlingerQuasiGeodesicLeastArea_closed : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}` := `relativeGreendlingerQuasiGeodesicLeastArea_of_inputs o52LeastArea h94 hin`.
  - Land now: `osinSection97Inputs_of_parts` (hin from its four parts) and the assembly over explicit h94 and part Props.
  - Flip to closed as the parts land.
- Also: `HullSC.HullRelatorRespellingStatement`, if any consumer remains after theoremc-retire.

## hull-bridge  (clone rank-four)
- Predecessor report: `hull-bridge.md`.
- Target: a producer of `QuotientPeripheralLetterPullbackStatement`, then the closed `relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0,0,0}`.
- You are the integrator: split off sub-lemmas for hull-component in your first report.

## hull-component  (clone ring-b-alg)
- Predecessor: `$NM/lanes/hull-component.files` (6 files). hull-bridge.md mentions the Rotate red fix.
- Target: first make the red Rotate/component modules green and land them; then prove the pullback sub-lemmas hull-bridge assigns.

## kh-torsion  (clone ring-b-end)
- Predecessor report: `kh-torsion.md`. Also read `go-sr1.md`: 9d2429b45 corrected the zip-spur producer.
- Target: closed hzip, `theorem zipSpur_cosetComplex : Systolic.ZipSpurStatement CCKW.cosetComplex` (`GGT/SystolicDiscZip.lean`).
- State the producer for every triangle complex X, because the hT6 route needs hfill at arbitrary X. Hand one case to systolic-counts.

## fff-periodic  (clone spare1)
- Predecessor report: `fff-periodic.md`.
- Target: closed hfold, `Systolic.MirrorFoldStatement CCKW.cosetComplex`.
- State it for every triangle complex X, because both hyperbolicity and hT6 use it. Hand one case to ko-closed.

## systolic-counts  (clone stw-fix)
- Predecessor reports: `systolic-counts.md`, `go-sr1.md`.
- Done 09-13: `GGT/SystolicDiscCounts` is closed on main, and so are ha, hb, hc, hcount and hsum.
- Now: one case of hzip (`ZipSpurStatement X`, arbitrary X), handed off by kh-torsion.
- Also: the filling inputs `ha hb hc hd` of `fillingStatement_of_simplyConnected` (`GGT/SystolicDiscFilling.lean:126`), and `hcount hsum` for the alternative KO route.

## kh-cckw  (clone thm-d)
- Predecessor report: `kh-cckw.md`. The ball-dismantling stage-1 probe was green (b157143e3); read `leavitt-ge.md` on the systolic ball-dismantling module.
- Target: closed hT6, `CCKW.SystolicInvariantCliqueStatement` (`GGT/SystolicDismantlable.lean`, `GGT/SystolicGraphConditions.lean`).

## ko-closed  (clone thm-e)
- Predecessor report: `kh-hyperbolic.md`.
- Target: new `Kazhdan/KotowskiOllivierClosed.lean`.
  - Now: `theorem kotowskiOllivier_of_leaves (hzip ...) (hfold ...) (hT6 ...) : TheoremC.KotowskiOllivierStatement`.
  - Then `theorem kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement` as the leaves land.
- Hand to: theoremc-retire (`TheoremCAssembly` :653) and nm-endpoints.
- Done 09-13: `kotowskiOllivier_of_leaves` is green (c5a8ae8fb).
- Now: one case of hfold handed off by fff-periodic, and the dedupe of the orphan `Kazhdan/KotowskiOllivierLeaves`.

## simple-group  (clone xxii-fix)
- Predecessor report: `simple-group.md`.
- Target: INTEGRATOR of hW, `theorem finitelyPresentedInfiniteSimple_closed : FinitelyPresentedInfiniteSimpleStatement` via `finitelyPresentedInfiniteSimpleStatement_of_stabK` with `h47 : StabKFinitelyPresented qTwo` (Hyde–Lodha Prop 4.7).
- You own the Prop 4.7 assembly. Split: hl-lemma46 has Lemma 4.6; fff-quotient has the product and normalization pieces; kh-ejz has the finite-presentation transfer (PiFinitePresentation).

## hl-lemma46  (clone cs-endpoint)
- Predecessor: none by name. Read `simple-group.md`.
- Target: Hyde–Lodha Lemma 4.6, closed, at the generality Prop 4.7 consumes.
- 09-13 final split. The interface is simple-group's `QTwoLemmaFourSixStatements` (232d6b12b):
  - hl-lemma46: `LemmaFourSixDynamicsStatement`.
  - simple-group: `lemmaFourSixCaseOne_of_dynamics` and the final closed endpoint.
  - kh-ejz: the casing pair plus conjugation of a general [a,b] into the unit frame.
  - fff-quotient: |I| = 1, as an ascending HNN over a shorter base.
  - simple-group names the kh-ejz and fff-quotient Props.

## fff-quotient  (clone cs-limit)
- Predecessor: `$NM/lanes/fff-quotient.files` (16). The Prop 4.7 product and normalization modules probed green at 19258411c.
- Target: the remaining Prop 4.7 pieces, other than Lemma 4.6 and PiFinitePresentation, closed.
- Done 09-13: Restrict, StabKSplit, StabK, GermGamma, Long and PropositionFourSeven, all green.
- Now: Lemma 4.6 with |I| = 1, as an ascending HNN over a shorter base. simple-group names the Prop.

## kh-ejz  (clone cs-simplicity)
- Predecessor report: `kh-ejz.md`.
- Done: PiFinitePresentation (ba54a571f).
- Now: the Lemma 4.6 casing pair plus the unit-frame reduction. simple-group names the Prop.
- Then: row LINE:1675 (FFF paragraph), with nm-endpoints.

## theoremc-retire  (clone cs-stages)
- Predecessor: none. See census2 U2.
- Target: zero `sorry` in root-imported `Manuscript/NonMF/TheoremCAssembly.lean`.
  - Retire the four sorry declarations `estimatingSelectionConstruction`, `estimatingUnboundOutput`, `relativeIsoperimetricBridgeQuasiGeodesic` and `hullRelatorRespelling`.
    - They are consumed: `hullLemma44FamilyInclusionJoint` uses all four, and :518 uses it.
    - Re-route :518's consumers through the least-area route, then delete the chain.
    - Do not prove `HullRelatorRespellingStatement`: it is too strong as printed.
    - Grep consumers on origin/main first, and probe every user (rule 22).
  - Replace the `kotowskiOllivier` sorry. Consume ko-closed's `kotowskiOllivier_of_leaves` only in intermediate lemmas; the endpoint closes when ko-closed lands.
  - Re-point `Manuscript/MFRecognition/SeedFromTheoremC.lean` at the least-area route.
  - Fix docstrings that say "five sorries".
- Never delete files. Probe `GroupApproximation.Manuscript.NonMF.TheoremCAssembly` together with every importer.

## nm-endpoints  (clone quant-collapse)
- Predecessor: `$NM/lanes/nm-endpoints.files` (26); `sec5-sentences.md`.
- Target (census2 U7), the closed top endpoints:
  - `printedTorsionFreeTheorem : PrintedTorsionFreeTheorem`;
  - `printedRegularNonMFAlgebra : PrintedRegularNonMFAlgebra`, via `manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO`;
  - `fournierFacioParagraph : FournierFacioParagraph`;
  - `literatureInputs : TheoremC.LiteratureInputs`;
  - the closed saturation and thm:hull forms;
  - the carrier-debt `TheoremC.Configuration` (row dab2f2bfe084).
- Now: land `*_of_fourLeaves` forms that take exactly the four wall Props, so each flips to closed with one line. Flip them as the walls close.
- Rows: L66 (the torsion-free half), L285, L291, L1637–L1719.
- Also: the open-predicate baseline findings that are only "over the least-area leaves" (Hull 7.1 leaves or Hyde–Lodha).

## cite-hull  (clone lix-a)
- Predecessor report: `cite-hull.md`.
- Target: Hull Theorem 3.12, Corollary 5.7, Lemma 5.8 and Corollary 7.4 as PROVED theorems at the printed generality.
  - 18de0ce6a carried them as sentences; check whether those carriers are closed.
- Rows: L1629, L1644, L1659, L1675 (the Cor 7.4 half, with nm-endpoints).

## sec5-sentences  (clone lix-b)
- Predecessor report: `sec5-sentences.md` (32 files in flight).
- Target: every proof-step sentence of §5 (tex 1621–1737):
  - rows 721da4c14d11, 2d1cd22e5f49, 2f997e5af4e6 and bcc99703f838;
  - a9dd4b90e479: re-grade it, since `isAcylindricallyHyperbolicOsin_of_limitSet` landed at 6b5a5f75e;
  - each `_of_leastAreaLeaves` sentence carrier gets a `_of_fourLeaves` form, flipped to closed as the walls land.
- Hand OsinUnboundMerged to hull-unbound, naming the files in your first report.

## ghw-assembly  (clone lix-c)
- Predecessor reports: `ghw-charp2.md`, `dgo-geometric.md`, `sec2-sentences.md`. Also commit 857f7e44a ("Reduce GHW Theorem 4 to its prime and zero characteristic cases").
- Target (census2 U4): `def PrintedGHWTheorem4 : Prop := ∀ (K : Type) [Field K] (Γ : Subgroup (GL (Fin 2) K)), Countable Γ → HasHaagerupProperty.{0,0} Γ` and the closed `theorem printedGHWTheorem4 : PrintedGHWTheorem4`.
  - Check the exact `HasHaagerupProperty` signature and the 857f7e44a reduction first.
- Row: b6d1590be7ab L1145. Consumers: JacobsonRankTwo, JacobsonLaurentKazhdan.

## ghw-charp2  (clone lix-e)
- Predecessor report: `ghw-charp2.md`.
- Target: closed GHWCharP, the positive-characteristic places, at the Prop the 857f7e44a reduction consumes.

## dgo-geometric  (clone lix-f)
- Predecessor report: `dgo-geometric.md` (29 files in flight).
- Target: closed GHWCharZeroFiniteness.
- Also: GHWArchimedeanBound and GHWArchimedeanSeparation green; land the in-flight files.

## sec2-sentences  (clone lix-g)
- Predecessor report: `sec2-sentences.md`.
- Target: closed GHWCountablePlaces.
- Also: the intro rows (tex 85–345) still partial. Row 61827aea7807 (L187) is joint with hs-vanishes: you own CompressionCriterionSentences, hs-vanishes owns NormalKazhdanPrintedRoute.

## hs-vanishes  (clone lix-h)
- Predecessor: none. See census2 U5.
- Target: a closed `NormalKazhdanPrintedRoute.manuscriptPrintedNormalKazhdan` with no HSVanishes binder, or an in-repo producer of HSVanishes for the printed K.
- Findings to retire: the carrier-data finding on row c36b6021a802, and the open-predicate finding on `Manuscript.OneSidedMFRadical.manuscriptPrintedNormalKazhdan`.

## baseline-debt  (clone lix-i)
- Predecessor: none. See census2 U6.
- Target:
  - (a) the open-predicate `NonMFSentences.FullDefectCornerRemark.manuscriptSentence_cornerPassesUp`. If the premise is the printed hypothesis of the sentence, make the case to the census lane, which reclassifies the finding; otherwise close it.
  - (b) the inlined-statement `TorsionFreePrintedSentences.manuscriptSentence_theoremQuotientTrivial`.
  - (c) discharge `ReducedGroupCStarTrace.powersAveragingEstimate_of_naiveFreeProductProperty` with the closed, rooted `naiveFreeProductAtAcylindricallyHyperbolic`.
  - (d) the two IsStronglyOperatorMF lines. cite-cstar says they are the proved contrapositive: verify, then fix the carrier or have census fix the finding.
  - (e) the carrier-data lines and the 9 carrier-debt lines in Manuscript.NonMF: a closed carrier for each.
  - (f) the open-predicate findings that hs-vanishes and nm-endpoints do not own. Classify them as debt-conditional does, close those that are not walls, and report the residue with exact Props.

## jacobson  (clone lix-j)
- Predecessor: `$NM/lanes/jacobson.files` (33).
- Target: the four unassigned L1122 rows: the Toeplitz–Jacobson algebra J; JeJ = finite matrices; ker(EL_n(J)→EL_n(F2[z,z^-1])) ≤ GL_fs(V^n); equality of the inclusion.
  - Modules: JacobsonSymbol, JacobsonFiniteMatrices, JacobsonKernelFinitary.
  - `jacobson.tsv` already says LINE:1122 formalized; verify the carriers are closed.
- Then: L1145 c149d33e8f7e, the complementary sentence (after ghw-assembly lands).

## leavitt-units  (clone lix-k)
- Predecessor report: `leavitt-units.md`.
- Target: row 7916c8696def L1307, a closed `LeavittMFQuotientSentences.manuscriptSentence_unitsEquivGL` (LeavittMFQuotientUnitsGL draft).
- Then: audit the cor:leavitt-mf-quotient block (tex ~1250–1323) for rows that are not closed.

## census  (clone census)
- Predecessor reports: `census2.md`, `notes/nm-swarm/census-notes.md`. Tools: `$NM/census/`.
- Target U3: re-merge every `metadata/nm-census-rows/*.tsv` into `metadata/NON_MF_SENTENCE_MAP.tsv`.
  - Match rows by sentence text, never by line number.
  - Regenerate `metadata/NON_MF_SENTENCE_CENSUS.md` and `notes/nm-swarm/WORKLIST.md`.
  - Run `scripts/sentence_census.py --verify-unconditional` on MSI through `census_run.sh`, never locally.
  - Remove the baseline lines that lanes report retired.
  - Re-merge about every 2 h and report the counts to the lead each time.
- You own the map, the census md, WORKLIST.md and both baseline files.

## audit-intro (clone lix-l): tex 1–784 · audit-sec3 (clone lix-m): tex 785–1620 · audit-sec5 (clone lix-n): tex 1621–2022
(One audit module per manuscript section in your range.)
For EVERY census row in your range with status formalized or definition, and every structural, attribution or provenance row that contains a mathematical claim:
1. The named declarations exist on origin/main and are reachable from the root.
2. Write the audit module `Manuscript/NonMF/Audit/<Range>.lean` (e.g. `Sec2.lean`). It imports the carriers and runs `#audit_closed_axioms` on each named-Prop endpoint and `#audit_axioms` on each lemma (rule 19). Probe it and land it; it becomes a permanent gate.
3. Read each carrier's statement against the printed sentence: verbatim generality, printed route, no literature binder, no hypothesis the sentence does not print.
4. Fix a defect with a closed carrier in a NEW module and land the corrected row.
   - A defect that is another lane's wall: report it to the lead instead.
   - A row with no carrier at all: write one.
- Put the finished audit module on the wire queue.

## debt-conditional  (clone lix-r)
- Target: the 32 buried-conditional findings (27 Manuscript.NonMF, 3 HullSC, 2 GGT.RelHyp) and the 27 conditional-debt findings (22 Manuscript.NonMF, 4 HullSC, 1 GGT.RelHyp) in `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`.
  - Classify each one first. If its only open inputs are the four wall binders, list it in your report and stop there: nm-endpoints re-routes those once the walls close. Do not build parallel wrappers.
  - For the rest (the HullSC and GGT.RelHyp findings, and any other input that is not a wall), discharge the buried hypothesis with an existing closed producer, or write a closed carrier.
  - The census lane removes the baseline lines you retire (row note "retires <kind> <decl>").

## root-wire  (clone lead)
- Predecessor: `notes/nm-swarm/wire-queue.txt`, census2 U8. Tools: `$NM/nmwire.sh`, `nmwirelist.sh`, `dupcheck.py`, `closure.sh`.
- You are the ONLY lane that runs nmwire.sh. It builds the root in the lead clone and lands only on ROOT GREEN.
- Initial queue: TorsionFreeSectionAssembly, CCKWTitsGHB, GHBHyperbolicFilling, GHBHyperbolicDiscCounts, GHBSharpExistenceSystolic, GHBLatticeRouteKazhdan, SystolicDiscFilling, SystolicDiscZip, SystolicDismantlable, GHWArchimedeanBound, GHWArchimedeanSeparation, OsinCitedSentencesClosed, SoficCitationSentences, EJZCitationSentences, GammaBarKazhdanSentences, IntroSentences; SystolicDiscCounts once green. Then each lane's lines in `$NM/wire-queue.txt`.
- Before each wave:
  - run a duplicate-declaration check (compare content, not only names) and a cycle check;
  - never wire a module whose last probe was red;
  - read the memory files on the root docstring import trap and on transitive dangling imports.
- Also compute the census-carrier modules that are not reachable from the root, and wire them.

## Reassignments 09-13 ~02:00 (lanes whose targets closed, sent to open wall pieces)
- W1 pocket cut core. This blocks SectionPocketCut, MultipleEdgeCut and LoopCut, and hull-euler's empty 2-gon pocket.
  - dgo-analytic owns it, in new `Estimating/OsinPocket*` modules: (a) the face set enclosed by a closed walk, with its embedded boundary; (b) the least-area cut with four sections; (c) glue-back transport.
  - Proposed split: (b) to hull-select, (c) to go-lemma42.
  - hull-respell: the shelling producer (`FaceSetEarStatement`, `VanKampen/FaceSetPeelProducer.lean:171`).
  - nm-endpoints: `OsinDescentStepInput`, or whichever piece dgo-analytic gives it.
  - hull-euler consumes (a) for its pocket extraction.
- W1 h94: `OsinLemma94RunInput.no_connector` is not provable unoriented, since the planar Case 1 only contradicts antiparallel pairs.
  - hull-count94 owns a new oriented metric layer (oriented Lemma 25 for polygons with at most 8 sides, OrientedSidePair/ClassPair, the three-class lemma, a monotone Morse index, WordConnectorPair target_backward) and restates RunInput/Counting on it.
  - sec5-sentences helps with one piece. Its four sentence forms flip when W1 and W2 land.
- W2 M2 split: hull-component writes `HullSCLemma51LetterPullbackCutFaces` (five cutFace_* lemmas). hull-bridge writes CutOutcome, Cut, Holds and EmbeddedBridgeHolds.
- W3 hT6: theoremc-retire helps kh-cckw. `Systolic.exists_invariantClique_of_neighborSet_finite` and "systolic balls are dismantlable" are absent from main; their owner sec4-sentences is dead.
- W4: leavitt-units helps hl-lemma46 with `LemmaFourSixDynamicsStatement`. kh-ejz owns `UpsilonShortOfCaseOne`; its Case 2 draft is orphaned at 9711ad726.
- GHW char 0: moved from dgo-geometric to ghw-assembly (`Kazhdan/GHWCharZero`, `Algebra/IntegerGridFinite`), which consumes sec2-sentences' closed `GHWCountablePlaces`. ghw-charp2 takes a piece, e.g. the places over ℚ.
- Baseline: hs-vanishes takes the operator-algebra findings, agreed line by line with debt-conditional.
- Orphans left on main, unwired, no deletion: GHWEntries (87790c4fa, dedupe by ghw-assembly), IntroLimitingTraceSentence (duplicate of sec2-sentences' L187), TorsionFreeKOLeaves and KotowskiOllivierLeaves (superseded by kotowskiOllivier_of_leaves).
- Stale-docstring backlog, parked: 14 modules that name retired TheoremC declarations (list in theoremc-retire.md); scripts/TheoremCCompletionAudit.lean; MF_RECOGNITION_SENTENCE_MAP row c6172bdc109a.

## Reassignments 09-13 ~02:30

- **W4 hW.** hW now depends only on `LemmaFourSixDynamicsStatement`.
  - simple-group: QTwoLemmaFourSixAssembly landed at 3e2e73c3d, probe green. It adds `finitelyPresentedInfiniteSimple_closed` once the dynamics module is green.
  - hl-lemma46: landed a full proof, `lemmaFourSixDynamics`, at de535e84c. Unverified; the probe is running.
  - Freed: fff-quotient (|I|=1 was proved by simple-group), kh-ejz (done), and leavitt-units (its duplicate draft stays unlanded in scratchpad lu-hl/).
- **W3 hKO.** hT6 is proved except hzip and hfold, at every X (kh-cckw, 7d64d1118). The KO route drops the hT6 binder. Residual:
  - (a) `ZipPinchStatement`: systolic-counts. kh-torsion offers to take the spur subcase; its fallback is a W1 PlanarRunInput piece from hull-unbound.
  - (b) `MirrorFoldDistinctStatement`: ko-closed. kh-cckw offers a split; its fallback is a hull-unbound piece.
  - (c) `MirrorFoldPinchedStatement`: moved to theoremc-retire, since fff-periodic had no landing this campaign and was asked for status. theoremc-retire also flips TheoremCAssemblyKOLeaves to `_of_leastAreaZipFold`.
- **W1 h94.** hull-unbound replaced `no_connector` with `osinLemma94Section_of_pieces` (b8441172e).
  - `OsinLemma94AntiparallelMetricStatement`: hull-count94, helped by sec5-sentences and hs-vanishes (two unstarted oriented-layer pieces).
  - `OsinLemma94PlanarRunInput`: hull-unbound.
  - `OsinLemma94RunInput` and `OsinLemma94Counting` are superseded.
- **W1, other helpers.** kh-ejz takes a part of `PhiPrimeCountInput` from hull-euler.
- **W2 hbridge.** debt-conditional and leavitt-units each take one of CutOutcome, Cut and Holds from hull-bridge. fff-quotient takes a part of CutFaces from hull-component.
- **Hull Corollary 7.4 at printed generality.** cite-hull takes K(G), AH0, Lemma 5.10 and Corollary 7.3 over the walls. baseline-debt takes general Lemma 3.5.
- **Audits.**
  - audit-sec5: probe and queue TorsionFreeAlgebraSentencesClosed, then audit the truth of the W1 and W2 leaf Props.
  - W3 leaf truth audit: whichever of audit-intro and audit-sec3 finishes first.
- **census.** Re-baseline after 2c3c8cb40, which predates no merge yet. Retire the 19 historical carriers debt-conditional classified. Register baseline-debt's retirements (a)-(d), and hs-vanishes's lines 66 and 79.
- **Hygiene.**
  - sec2-sentences: the stale TheoremC docstring backlog.
  - baseline-debt: audit-sec5's three docstrings.
- **root-wire.** Wave 1 root build was red only on `OsinUnboundSharedEdge` (hull-unbound: whnf timeout at :147, instance failures at :227 and :251). Rerunning the other 107 modules merged with wave 2.

## Reassignments 09-13 ~02:50
- **W4 hW CLOSED.** `finitelyPresentedInfiniteSimple_closed` landed in 47b31bef8. It is wired into the root through wave 2 (c72bdfd5d, 116 modules). simple-group's next item is an unstarted Hull Corollary 7.4 piece from cite-hull.
- **W3 hKO.** `ZipPinchStatement X` is closed for every X (d74b84054, probe 0913-023335-5925 green); kh-torsion wires it with SystolicDiscZip. Two cases remain:
  - `MirrorFoldPinchedStatement`: fff-periodic, with systolic-counts taking an unstarted subcase.
  - `MirrorFoldDistinctStatement`: ko-closed. kh-cckw offers b1/b2 (pending-digon deletion c88b8c1db is on main).
  - theoremc-retire takes a PlanarRunInput piece from hull-unbound. Theorem C is now over hgreendlinger, hbridge, hzip and hfold (e1b326ec3).
- **W1 cut core.**
  - hull-select's `i ≠ j →` binder on `MultipleEdgeCutInput` is approved. It lands as one landing across the Prop, SectionInduction and DescentInduction (dgo-analytic's file).
  - dgo-analytic is asked to fix the (a) carrier now.
  - go-lemma42 stopped at 01:19 on a usage-limit error and was resumed once on the (c) LoopCut piece. It must produce the `OsinMultipleEdgeCut.transport` shape.
- **W2 hbridge.**
  - hull-bridge writes LetterPullbackCutOutcome, Cut, Holds and EmbeddedBridgeHolds on hull-component's CutSides (14850636f), and hands two of them to debt-conditional and leavitt-units.
  - hull-component keeps CutFaces with fff-quotient and does not start the other four. After that it takes a Corollary 7.4 piece.
- **GHW char 0.** ghw-charp2 closed the places item (d2cf04137, 321615044, probe 0913-024239-39237). It owns the orphan `Algebra/IntegerGaussValuations.lean`, and next takes grid finiteness or the archimedean places from ghw-assembly.
- **census.** The merge at 94bb0a9f8 gives 498 rows: 306 formalized and 59 partial. The baseline has 132 findings, verify-unconditional reports 0 new, and verify-decls 0 missing.
  - New rule: a formalized row needs every carrier module in the root import closure.
  - Blocker: `JacobsonComplementarySentence` has no importer, queue line or green record; sent to jacobson.
  - The lead landed the missing `metadata/nm-census-rows/hull-count94.tsv`.
- **Audits.** The W3 leaf truth audit (MirrorFoldPinched and MirrorFoldDistinct for arbitrary X) moves to dgo-geometric. Its GHW Archimedean items are green and wired, and no audit lane was free.
  - dgo-geometric's `Algebra/IntegerPolynomialUnisolvence` (4896458dc) duplicates ghw-assembly's IntegerGridFinite. It is red with a sorryAx and stays an unwired orphan: no fix and no deletion.

## Reassignments 09-13 ~03:35
- **W1 (a) carrier: RULED by the lead.** dgo-analytic did not answer two nudges. The carrier is the outside face set with `IsDiscRegion`, and the piece is `DiscDiagram.ofPlanar` on `replaceGRegion`. There is no rebased full `RegionCutData`.
  - Why: a rebased copy needs a shelling of the pocket along the walk. That is `RegionShellingStatement` (FaceShelling.lean:194), which main flags as "the one planar fact still missing", with no producer.
  - `DiscDiagram.LeastArea` is algebraic (OsinAppendixSections.lean:112). So the piece's least area needs only a weighted form of the closed `isRelatorProduct_of_planar` (PlanarVanKampen.lean:122) on Δ with the pocket collapsed.
  - kh-torsion (free after hzip): new `GGT/VanKampen/PlanarVanKampenWeighted.lean`, holding the weighted ear induction and the DiscDiagram corollary. Its C1 fallback on PlanarRunInput is withdrawn.
  - hull-select: the shelling-free carrier structure. It is additive, so RegionCutData and ofRegionCut stay. Also ports of diagram_boundaryWord, boundarySectionCuts, fourSectionCuts and leastAreaCut, and the ofPlanar analogue of `ofRegionCut`. It lands the structure statement first.
  - kh-ejz (free after the Euler multigraph Props, 04240bd43): the pocket geometry from a ≠ b. That is IsDiscRegion for both sides, the split s₁t₁s₂t₂, quasi-geodesic parts, short sides, and at least one kept cell.
  - go-lemma42: (c) retargets to the ofPlanar piece.
  - dgo-analytic: DescentInput only. It sends kh-ejz any carrier code it has, and re-grades or supersedes census LINE:1688.
- **W3 hKO.** hzip is CLOSED: `CCKW.zipSpur_cosetComplex` (8389a0e6c, #audit_closed_axioms, root-imported). The remaining leaf is hfold.
  - dgo-geometric's truth audit: `MirrorFoldDistinctStatement X` and `MirrorFoldPinchedStatement X` are both TRUE for every X, using only irreflexivity and tri_adj. The owners keep going; there is no restatement.
  - dgo-geometric next writes the nonvacuity fixture `GGT/SystolicDiscMirrorFoldModel` and checks the wiring of NaiveFreeProductPropertyOfAcylindricallyHyperbolic.
  - theoremc-retire: Theorem C over hgreendlinger, hbridge and hfold, in a new module specializing TheoremCAssemblyKOLeaves (e1b326ec3) at hzip := zipSpur_cosetComplex. Then C1 of PlanarRunInput if hull-unbound hands it over.
- **W1 h94.** hull-unbound has two open items: the Case 2 minimality measure (theoremc-retire proposes dart count) and the OsinUnboundSharedEdge red.
- **census merge 4** (86df293af): 340 formalized, 23 partial (down from 59). Five carrier modules are unwired, and JacobsonComplementarySentence is still blocked.
- **root-wire** was sent on wave 3 over queue entries since c72bdfd5d, plus the census's unwired carriers that have green records.

## Reassignments 09-13 ~03:55
- **W1 (a) carrier, update.**
  - The weighted planar van Kampen item is dropped. dgo-analytic's `Estimating/OsinPocketOuterPart.lean` (c0a1c1bee) already proves the outer-part exchange (`DiscDiagram.exists_isRelatorProduct_of_discRegion`, `LeastArea.length_filter_mem_le`), so least area of the piece is covered.
  - **Collar ruling.** hull-select found that the quasi-geodesic requirement of SectionCuts cannot hold on short side arcs: a spur `x x⁻¹` has length 2 and distance 0, and c = 0 is allowed. This affects MultipleEdgeCut, LoopCut and SectionPocketCut.
    - Fix: pass to an O-equivalent Δ' with a G-face collar along each side arc. The collar is a path labelled by a geodesic word g_j with |g_j| ≤ ε, and hquasi follows from `isLambdaCQuasiGeodesicWord_of_geodesic` (CutSections.lean:160).
    - Main has no surgery that attaches a face along an arc.
  - hull-select: lands the collar statement first, unverified, then the carrier structure and ports.
  - kh-torsion: proves the collar insertion, spur sides included, plus IsDiscRegion for both sides of g₁ t₁ g₂ t₂.
  - kh-ejz: region-side data. The sides only need |s_j| ≤ ε and need not be quasi-geodesic; t₁ and t₂ must be quasi-geodesic; the kept cell is unchanged.
  - go-lemma42 (LoopCut) and dgo-analytic (SectionPocketCut) consume the same collar lemma.
  - hull-select lands the `i ≠ j` DescentInduction patch under the approved binder without waiting for dgo-analytic. Disk = main f82dfe0c3f, and the SectionInduction probe 0913-032524-67109 is green.
- **W1 PhiPrimeCountInput.** hull-euler landed (J), `CombMap.IsRestriction.faceOf_eq_of_faceClass` (9fdb80035, probe 0913-032836-75226 green).
  - Plan: C1–C6 over Osin Lemma 9.3, consuming kh-ejz's multigraph bounds.
  - C6 (empty two-gon → False) is stated as a named piece Prop in hull-euler's module, with hypotheses shaped for the ofPlanar carrier. kh-ejz and hull-select discharge it.
- **W1 h94.** `OsinLemma94AntiparallelMetricStatement` is CLOSED by sec5-sentences: `osinLemma94AntiparallelMetric` (e3da1ba60) on `unboundOrientedWordPolygonMonotone` (779509227), probe 0913-034427-9910 green.
  - The residual of `osinLemma94Section_of_pieces` is `OsinLemma94PlanarRunInput` alone (hull-unbound; C1 goes to theoremc-retire).
  - sec5-sentences takes a case from hull-unbound. If hull-unbound is silent, it takes Case 2 with the dart-count measure in a new module.
- **W3.** Theorem C over hgreendlinger, hbridge and hfold landed (f019265bb, `TheoremCAssemblyFoldLeaf`). Mirror-fold stages on one side of a split map landed (e12190690, `SystolicDiscMirrorFoldRestrict`).
- **GHW char 0.** ghw-charp2 closed item 3: `IntegerPlacesMinpoly.exists_places_minpoly_coeff` (0379bac08, probe 0913-033545-85262).
  - The residual `GHWFinitelyGeneratedCharZero` is the archimedean places plus assembly. That belongs to ghw-assembly, whose `Kazhdan/GHWCharZero.lean` is unlanded on disk.
  - ghw-charp2 takes a piece that ghw-assembly names. First it probes and queues `JacobsonComplementarySentence`, because jacobson has been silent since ~02:50.
- **census merge 6** (88289a4ee at 5f9c16b7b): 340 formalized, 26 partial; baseline 135, 0 new.
  - 8 partial rows are waiting only on wiring: IntroConventionSentences, LeavittMFQuotientUnitsGL, FullDefectPairLeavitt, StrongConvergenceMFSubsingleton and JacobsonComplementarySentence.
  - LINE:1688 is still skipped (dgo-analytic).
- **root-wire.** Wave 2 is ROOT GREEN at c72bdfd5d (116 modules). Wave 3 (17 modules) is building at cdc493958.
  - Held: Audit.Sec3 (no probe names it; sent to audit-sec3).
  - Held: OsinLemma94Pieces and OsinUnboundSharedEdge (red 0913-022343-56095). Pieces is built transitively by the green 0913-034427-9910.
  - Held: LeavittMFQuotientUnitsGL (no record; sent to leavitt-units) and JacobsonComplementarySentence (no record).
- **Refuted shelling Props.** Both confirm the ofPlanar ruling, since that route consumes no shelling.
  - `Embedded.FaceSetEarStatement` is FALSE (hull-respell, `not_faceSetEarStatement`, 9dda53a05, green 0913-025312-66955). The counterexample is a spur inside a G-face with no peelable ear.
  - `RegionShellingStatement` is refuted by audit-sec5's RegionShellingSpurCounterexample, not landed yet.
  - The binders on the false Props: FaceSetPeelProducer.lean:182 and :194, PieceConstruction.lean:30, :56 and :83, PieceCore.lean:228. The corrected form must allow alpha-pair erasure.
- **hull-respell** (pocket shelling redundant): offers kh-torsion the IsDiscRegion-both-sides half (edge-deletion induction on reclosedMap). kh-torsion decides the split.
- **kh-ejz** landed text fix 46f1c36a2 (stale hKO docstrings). It stays on pocket geometry, and PhiPrimeCountInput (A)/(B) stays with hull-euler.
  - kh-ejz also owns the loop pocket for LoopCutInput: target = some source; walk s t with s a collared side and t a cell arc; IsDiscRegion, FollowsBoundary, a kept cell, and the `CyclicArc` arc datum on each cell part.
- **go-lemma42** (c): `DiscDiagram.regionPiece_transport` and `OsinLoopCut.ofRegionPiece`.
  - Y glues an O-equivalent copy Xi into Δ' along the region cycle, via ofPlanar. Planarity comes from χ(Y) = χ(Xi) + χ(Δ') − χ(piece) = 2 through `reclosed_isRestriction`, with no new hypothesis.
  - New modules, not landed yet: SurgeryPocketGlue, SurgeryPocketGluePlanar, Estimating/OsinPocketGlueDiagram, Estimating/OsinPocketGlueTransport.
- **W1 carrier reconciled with dgo-analytic's split (~04:05).** dgo-analytic's `PocketRegion` (Estimating/OsinPocketRegion.lean, in probe) IS the ruled carrier. It has faces and outside with inner and outer IsDiscRegion and cycles matching up to rotation; its diagram is ofPlanar on the collapse, and it provides diagram_boundaryWord and diagram_leastAreaCut.
  - RegionCutData is unbuildable: its shelling producer went through the refuted FaceSetEarStatement, and cells_infix is circular. So OsinPocketLeastAreaCut and ofRegionCut stay unused.
  - (a) producer: dgo-analytic integrates and states the piece Props in OsinPocketPieces.lean, collared form included. The discharges:
    - kh-ejz: region-side data, a ≠ b and loop.
    - kh-torsion: collar insertion.
    - hull-respell: pinched pocket (simple circuits, or 0-refinement), so that `FaceSetCircuits.toDiscRegion` (FaceSetBoundaryEnumeration.lean:122) gives both sides.
    - dgo-analytic: PocketRegion, assembly, DescentInput.
  - (b) hull-select: rebase boundarySectionCuts, fourSectionCuts and fourSectionCuts_leastAreaCut on PocketRegion.diagram, with no separate structure.
  - (c) go-lemma42: transport against PocketRegion.diagram, including cellTransport and sectionTransport for SectionPocketCut.
  - hull-euler: its C6 Prop is shaped on PocketRegion.
- **root-wire wave 3 ROOT GREEN** at ce699b9b8 (17 modules, closure 6214, 0 dangling). It includes the Olshanskii oriented layer, GHWCharZeroPlaces, UnboundMonotoneMorseIndex, UnboundOrientedWordConnectors, OsinAppendixEulerMultigraph, IntroConventionSentences, Audit.Intro, Audit.Sec2 and Audit.Sec4, AffineDoublingLiteralModel, and three census carriers.
  - Wave 4 staging:
    - OsinLemma94Pieces, accepted on a transitive green build;
    - UnboundOrientedWordPolygon and OsinLemma94AntiparallelMetric;
    - HullLemma35Printed;
    - LeavittMFQuotientUnitsGL (green 0913-040613-59510);
    - JacobsonComplementarySentence (ghw-charp2 green 0913-040230-50292).
  - Held: Audit.Sec3 and OsinUnboundSharedEdge.
- **Freed lanes (~04:10).**
  - sec2-sentences closed the stale TheoremC docstring backlog (2e93f09d1, 12738313c, 9ac39c698, 8f8b5ccab). It now takes a (c) transport module or instance from go-lemma42.
  - hs-vanishes: own target met (baseline lines retired at 63f147d7b). It now takes a W2 Lemma 5.1 certificate-cut piece from hull-bridge.
  - hull-count94: its newer AntiparallelMetric variant must NOT land over sec5-sentences' e3da1ba60; extra declarations go in a new module. It now triages the OsinUnboundSharedEdge red: route check first; fix only with hull-unbound's agreement and disk = main.
- **hull-unbound** has been silent since 02:31. Defaults stand unless it objects: Case 2 goes to sec5-sentences (dart count), C1 to theoremc-retire, and the SharedEdge triage to hull-count94.

## Reassignments 09-13 ~05:00
- **W1 leaf-audit rulings** (audit-sec5 report 160ed175c).
  - (a) One shared zero-cell pocket merge producer: the inputs of `false_of_collapse_singleton` (OsinAppendixCutMerge.lean:120). It serves the R-cell-free pocket of MultipleEdgeCut and of SectionPocketCut, and C6.
    - hull-select: statement, FaceSetBoundary on the union, merged ContiguityGeometry at {R.merged}, hweight, assembly. New module Estimating/OsinPocketZeroCellMerge.lean.
    - nm-endpoints: the value half with no shelling. On an R-cell-free PocketRegion, rCellCount = 0 (`diagram_rCellCount_le`), so the boundary is a budget-0 relator product, moved onto the pocket cycle by `isRelatorProduct_inner_of_diagram` (OsinPocketRegion.lean:177). New module Estimating/OsinPocketMergeRegion.lean.
    - The value never comes from `InnerGRegion.ofShelling`.
  - (b) `LoopCutInput` is on HOLD. audit-sec5 model-tests the cap:
    - |t| > 0: absorbing the pocket raises the weight, against weight_maximal; check the extended family is legal.
    - |t| = 0: excluded by RegionCandidate or label legality, or give a formal counterexample.
    - Since b45e7ef30 the case i = j also routes to LoopCut. No loop-case transport is built until the lead rules.
  - (c) `OsinDescentStepInput` is RETIRED (off route): a docstring note only, no deletion.
  - (d) `SectionPocketCutInput` belongs to dgo-analytic: the zero-cell case from (a), the pinched pocket from hull-respell.
  - The collar stays with kh-torsion: GGT/VanKampen/SurgeryGeodesicCollar.lean, or dgo-analytic's piece if that is on disk. PlanarVanKampenWeighted (16d5bf784) is a bonus, not relayed.
  - go-lemma42's (c) target is `OsinMultipleEdgeCut.ofPocketRegion` (hull-select, 45e7201da): transport for sections 1 and 3. One module goes to sec2-sentences.
  - dgo-analytic lands the OsinPocketPieces statement unverified now, re-grades LINE:1688, and adds the DescentStep off-route note.
  - dgo-geometric model-tests each new piece Prop as it lands: merge, collar, OsinPocketPieces, C3–C5.
- **W1 PhiPrimeCountInput split** (Osin 9.3).
  - hull-euler keeps C1 (Φ'') and the assembly, and states C2–C5 as named Props.
  - C2 (m+6 ≤ 3c+t): ghw-charp2. C3 (degree < 6 ⇒ two-gon): debt-conditional. C4 (corner injection): leavitt-units. C5 (face-class injection via (J)): hs-vanishes.
  - C6 consumes the merge of (a).
- **W1 h94.** hull-unbound states side_budget and covers as a piece Prop, which goes to hull-count94. hull-unbound keeps realization and the assembly. OsinUnboundSharedEdge is fixed and green (8009a06ff) and wired in wave 5.
- **W2 hbridge CLOSED** (~05:02). hull-bridge: `relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0,0,0}` (18682110d, probe 0913-050027-71372).
  - Built on `quotientPeripheralLetterPullbackStatement_holds` (HullSCLemma51LetterPullbackHolds), hull-component's `CutMove.outcome` (CutOutcome a1f2e52da, CutOutcomeSides 27f56e14b, CutOutcomeRight 47b7225af) and debt-conditional's `letterStepBound_of_cutLiftOutcome` (457c543a8).
  - leavitt-units' duplicate right case was dropped unlanded.
  - Flips: hull-bridge adds `_of_greendlinger` forms in new modules (74 baseline findings carry this binder); theoremc-retire specializes TheoremCAssemblyFoldLeaf.
  - ghw-assembly flips the closed-wall findings: FinitelyPresentedInfiniteSimpleStatement (8), zipSpur, zipPinch and SystolicInvariantClique (10 each).
- **census merges 8–10** (6fd3d7a55): 339 formalized, 23 partial, baseline 135 (61 open-predicate, 58 buried-conditional, 14 carrier-data). 0 new findings.
- **W3 hfold CLOSED** (~05:27). fff-periodic: `Systolic.mirrorFold (X) : MirrorFoldStatement X` (GGT/SystolicDiscMirrorFold 426813b24, probe 0913-052528-4751).
  - Chain: Stage c88b8c1db, Restrict e12190690, PinchedStage 08ae1c587, plus ko-closed's `mirrorFoldDistinct` (81b06b43e).
  - `kotowskiOllivier_of_pinched` (KotowskiOllivierClosed, cf1675f3b) needs only Pinched, so hKO closes as one application: ko-closed's `kotowskiOllivier_closed`.
  - Pinched helpers released: kh-cckw goes to hull-respell's pinched pocket, systolic-counts to a go-lemma42 glue module.
- **Only W1 hgreendlinger is open.** The flips are partitioned by consumer module. Each form consumes all closed producers and leaves hgreendlinger alone:
  - hull-bridge: Hull 7.1 / LeastArea modules;
  - fff-periodic: TorsionFreeFourLeaves, SectionSentencesFourLeaves, TheoremC.manuscriptTorsionFree*, other KO/MirrorFold binders;
  - ghw-assembly: Kazhdan, CCKW, KMSGroup and HydeLodha consumers of FPIS, zip and SIC;
  - theoremc-retire: TheoremCAssemblyFoldLeaf.
  - If a declaration looks like it's in two sets, the owner of its module wins.
- **Hull Corollary 7.4, wall-independent pieces.** cite-hull states them and hands them out:
  - K(G) (DGO 6.14): simple-group;
  - Hull Lemma 5.10: hl-lemma46;
  - AH0: fff-quotient;
  - Lemma 3.5 in general form: baseline-debt.
  - Corollary 7.3 over the two walls goes to hull-component. cite-hull keeps the Corollary 7.4 assembly.
- **GHW Theorem 4 CLOSED.** ghw-assembly: `ghwFinitelyGeneratedCharZero` (GHWCharZero, add35a53a) and `printedGHWTheoremFour` (GHWTheoremFourClosed, 66417a372), green 0913-044200-34335. ghw-charp2's bridge landed at 86635025c.
  - ghw-assembly next: the Jacobson rank-two consumer, stated over the printed field GL_2(F_2(z)); GHWEntries marked superseded in a docstring only.
- **Toeplitz–Jacobson CLOSED** (jacobson).
  - The four L1122 Props: JacobsonPresented ff4a0eea9 and JacobsonPresentedSentences cba3ce8ba, green 0913-043721-21532.
  - Complementary sentence: JacobsonComplementaryPresented e6dc0d444, green 0913-045006-54503.
  - Next: row 3009704fef89, two named Props with audit lines.
- **baseline-debt.** Fix the FaceShelling.lean:190 docstring (RegionShellingStatement refuted at 3f6eaff76), and re-grade the LINE:1725 row: P_naive is closed and wired per dgo-geometric.
- **root-wire wave 5 ROOT GREEN** a68ab2c6c: 10 modules, closure 6276, 0 dangling.
  - Wired: MirrorFold Steps, Quad, Embed and Model; IntroWitnessSignSentence; both spur counterexamples; RingCompressionCellGeneral; Audit.Sec3; OsinUnboundSharedEdge.
  - Wave 6 staging: the Cut chain with LetterPullbackCut, the GHWTheoremFourClosed chain, JacobsonPresented, its Sentences and ComplementaryPresented, OsinPocketCellArcs, GHWJacobsonKazhdanFinite.
  - 44 root import lines were added by hand by the open-problem campaign; wave 6 is the first root build over them.
- **census worklist** 0913-044759: 335 formalized, 27 partial. The partial rows are the walls (nm-endpoints 8, cite-hull 4 + 2, 1697, 1719, 1725) plus rows waiting on wiring (Jacobson 1122, ring-compression 872–904, GHW 1145).

## Reassignments 09-13 ~06:30

- **hKO CLOSED.** ko-closed: `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`, no binder (f65f99f17, probe 0913-055250-45566). It is `kotowskiOllivier_of_pinched (Systolic.mirrorFoldPinched CCKW.cosetComplex)`.
- **hT6 CLOSED.** kh-cckw: `CCKW.systolicInvariantClique` and `CCKW.cckwFiniteOrderConjugateIntoVertex` (hconj), in Kazhdan/CCKWSystolicInvariantCliqueClosed (61eddb4a9, probe 0913-061054-67459). `Hyperbolic.SharpExistence` closes the same way and goes to ko-closed.
- **Theorem C over hgreendlinger alone.** theoremc-retire: TheoremCAssemblyGreendlingerLeaf (c5f953323, probe 0913-060950-64731) and FoldLeaf (f019265bb).
- **Flip ownership, final.**
  - theoremc-retire: every TheoremC* module, the _of_leastAreaInputs forms and SeedFromTheoremC.E.
  - fff-periodic: TorsionFreeFourLeaves (38) and SectionSentencesFourLeaves (12). No Theorem C names.
  - ko-closed: nm-endpoints' five endpoint modules (LeastAreaAssembly, OsinNotion, HullPrintedLeastArea, LimitSetEndpoints, SectionAssembly: 27 findings), each in a new module; plus the row 8097c371f35d carrier swap to `_closed`.
  - hull-bridge: unchanged. ghw-assembly's set was only `kotowskiOllivier_of_leaves`, already superseded.
- **Hull Corollary 7.3 LANDED** by cite-hull (a2299c82c, HullCorollary73).
  - Correction: the ~05:00 handout of K(G), AH0 and 5.10 was stale. `finiteRadical`, `IsAH0`, `finiteRadical_eq_bot_of_suitable` (HullFiniteRadical) and `printedHullLemma510` (HullLemma510) were already on main. hull-component's Cor 7.3 draft is not landed.
  - cite-hull splits the Cor 7.4 route: free-product centralizer (jacobson), factor suitability with torsion (simple-group), first tower along inr(G2) (hull-component), f.g. second tower giving AH0 (hl-lemma46), countable case via 7.3 (fff-quotient). It adds `_of_greendlinger` forms of 7.3 and 7.4.
- **W1 zero-cell merge.** nm-endpoints' value half is OsinPocketMergeRegion (93cb4e04f, probe 0913-062000-78681): `Surgery.InnerGRegion.ofPocketRegion`, no shelling. The hrot interface is between it and hull-select.
- **W1 PhiPrimeCount.** hull-euler states C6's interface as `EmptyTwoGonInput` on PocketRegion (16d923f27). The shared merge produces it. C3–C5 statements go to debt-conditional, leavitt-units and hs-vanishes now; all three were idle.
- **W1 h94.** sec5-sentences: OsinLemma94DartMinimal (88db0df7b, probe 0913-062132-82302) proves `osinLemma94Section_of_planarRunInputReduced`, so the residual is `OsinLemma94PlanarRunInputReduced` (merged, pinch-split, dart-minimal families).
  - hull-unbound has not landed since 04:41, so the defaults stand: theoremc-retire states Case 1 and hull-count94 states side_budget/covers, each over the reduced hypotheses.
  - sec5-sentences takes the Case 2 exchange modules.
- **Other W1 landings:** go-lemma42 SurgeryPocketGlue (1e3497e4b); kh-ejz FollowsBoundary (d2b2ef55b).
- **root-wire wave 7 ROOT GREEN** 4a6cb4e55: 9 modules, closure 6301, every census carrier root-reachable. Wave 8 launched: HullCorollary73, TheoremCAssemblyFoldLeaf, JacobsonThreePlusOnePresented.
- **Stale partial rows** go to ghw-assembly to audit and re-grade: b6d1590be7ab, LINE:1688, LINE:1725, LINE:1155 (cite-ejz, no live lane) and LINE:1629.
- **jacobson.** All 26 rows are formalized. Next: transport PrintedJacobsonRankTwoKazhdanFiniteField to the presented J, then the Cor 7.4 centralizer.
