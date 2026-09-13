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
  - Correction ~06:40, superseding the two lines above:
    - ko-closed: the row 8097c371f35d carrier swap to `_closed`, and `Hyperbolic.SharpExistence`.
    - hull-bridge: its own modules plus nm-endpoints' five endpoint modules (LeastAreaAssembly, OsinNotion, HullPrintedLeastArea, LimitSetEndpoints, SectionAssembly: 27 findings). Its unlanded TorsionFreeGreendlingerForms and TorsionFreeGreendlingerSentences (06:36) already cover them. The ~06:30 assignment of those modules to ko-closed was retracted.
    - ghw-assembly's set was only `kotowskiOllivier_of_leaves`, already superseded.
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

## Reassignments 09-13 ~08:05

- **LoopCutInput is FALSE as stated** (audit-sec5).
  - At eps = 0 there is a cap counterexample: a region whose target is its own source cell, with an empty arc (GGT/VanKampen/LoopCutCapCounterexample, landing). It refutes LoopCutInput only for its W, not under OsinCCondition.
  - At eps ≥ 2, maximal families put caps in every two-dart gap.
  - Provisional ruling (A): loops leave the candidate class through a `RespectsSections` conjunct `target ≠ some source`. NoLoops then follows from `S.respects`, and LoopCutInput closes vacuously. (B) is out. (C), counting loops separately, is the fallback.
  - Before any edit to OsinAppendixSections:
    - ghw-charp2's read-only site census: every RealizedSectionFamily construction and every weight_maximal, card_minimal and RespectsSections use, on main and in drafts, with loop-freeness per site and patches kept in its backup;
    - audit-sec5's exact definition change;
    - one-line answers from hull-unbound (SingletonFaceRegion, OsinUnboundSharedEdge, the quadrilateral region), theoremc-retire (Case 1) and sec5-sentences (Case 2).
- **Separation for simple walks is on main.** hull-respell:
  - `simpleClosedWalkSides : SimpleClosedWalkSidesStatement` (GGT/VanKampen/SimpleClosedWalkSides, 4dce22f1e, probe 0913-072751-55574, `#audit_closed_axioms`);
  - `PocketRegion.ofSimpleClosedWalk` (Estimating/OsinPocketRegionSimpleWalk, a11a8d850, probe 0913-074604-81036).
  - The pocket producers consume these instead of rebuilding separation. Pinched walks (a repeated vertex) are hull-respell's, with kh-cckw.
- **SectionPocketCut pieces reordered.**
  - dgo-analytic's OsinPocketPieces (9cb70824c) put the collar before the pinch. kh-torsion showed `PocketCollarStatement` on a PocketFaceSet is not provable locally. Without FollowsBoundary the sides need not be edge paths, and a closed side of value 1 at a repeated vertex needs the pinch.
  - New order:
    1. pinch (hull-respell, `Collared` dropped);
    2. region (dgo-analytic: an uncollared carrier with both FollowsBoundary);
    3. collar (kh-torsion: `GeodesicCollarStatement`, e6d609771, applied twice with `withOuter`).
  - dgo-analytic restates the Props. kh-ejz takes `SectionPocketFaceSetInput` next.
- **Pinch gap in the zero-cell merge** (dgo-geometric).
  - `EmptyTwoGonInput` is true, but a discharge through `InnerGRegion.ofPocketRegion` (93cb4e04f) fails on pinched pockets: two regions meeting at one vertex give no FaceSetBoundary. The models are Estimating/OsinPocketPinchedTwoGonModel and ...Region (landing).
  - Route A goes to fff-periodic: collapse with `Surgery.MapCollapse.replaceGRegion`, take the value from `PocketRegion.listVal_inner_eq_one`, get one region by `ContiguityGeometry.ofSingletonFace`, transport the other regions, and so produce `EmptyTwoGonInput`. Route B is not taken.
  - hull-select states the merge over IsDiscRegion data; the target is a section or a second cell.
- **W1 PhiPrimeCount (Lemma 9.3).**
  - C3 closed by hull-euler (`exterior_of_isTwoGon`, c48f20f41); linked components by ghw-charp2 (cbca8029b).
  - `EmptyTwoGonInput` stays C6's interface.
  - C6′ (`f ∈ T → ¬HoldsCorner f → ¬HoldsCell f → False`): hull-euler states it, and debt-conditional proves it over simpleClosedWalkSides and hull-respell's pinched Prop.
  - C4 leavitt-units, C5 hs-vanishes. hull-euler keeps the assembly.
- **W1 h94 pieces.**
  - hull-unbound: `osinLemma94Section_of_planarPieces` (Estimating/OsinLemma94PlanarPieces, 80790fad1, probe 0913-070239-32512). The metric half is closed (e3da1ba60).
  - Piece owners and helpers: PolygonRealization, hull-unbound (ghw-assembly); PolygonCount, hull-count94 (audit-intro); CaseOne, theoremc-retire (ko-closed); CaseTwo, sec5-sentences (sec2-sentences).
  - sec5-sentences re-based OsinLemma94DartMinimal on PlanarPieces (b6bda9923, probe 0913-074213-73156) and retired the PlanarRunInputReduced forms. The ~06:30 defaults over the reduced input are superseded.
- **W1 MultipleEdgeCut.**
  - go-lemma42: SurgeryPocketGlueVertices (0cdb0dc87), SurgeryPocketGlueCount (3af801bac) and SurgeryPocketGluePlanar (291ae2c87, probe 0913-074643-82657). The glued map is planar and connected.
  - go-lemma42 next: Estimating/OsinPocketGlueDiagram, then the `htransport` of `OsinMultipleEdgeCut.ofPocketRegion` at j = 1, 3. FollowsBoundary is a hypothesis there.
  - kh-ejz's `MultipleEdgePocketRegionInput` (d00f94876) has no consumer yet. hull-select states the MultipleEdgeCut assembly over it, the collar, go-lemma42's transport and the merge.
  - hull-bridge helps kh-torsion with the collar steps.
- **Verifier defects** in `scripts/check_non_mf_unconditional.py`, found by census (merge 11 did not land; merge 12 runs with the corrected register.py).
  - False red on hKO. Namespaces are recorded only as the bare token and the full stack path, so a conclusion written as a partial path (`Manuscript.NonMF.TheoremC.KotowskiOllivierStatement` inside `GroupApproximation.KMSGroup`) never resolves. About 40 baseline lines rest on it.
  - Blind spot. A Prop structure built by an anonymous constructor (`CutLift`, HullSCLemma51LetterPullbackCut.lean:87) has no producer entry.
  - The script had no owner. systolic-counts fixes both, with a calibration fixture where a Prop with no producer still reports red. census then re-runs verify-unconditional on MSI.
- **Closed ~06:45–07:50:**
  - hull-bridge's flips 2aa98f8cc (HullSCGreendlingerForms, TorsionFreeGreendlingerSentences);
  - fff-periodic's TorsionFreeGreendlingerLeaf 1edf0f7b4: 23 forms, which covered nm-endpoints' five endpoint modules, so hull-bridge dropped its duplicate;
  - ko-closed's `Hyperbolic.sharpExistence_closed` (b0ab67b4a);
  - jacobson's `printedPresentedJacobsonRankTwoKazhdanFiniteField` (29632bb14);
  - kh-ejz's gap arcs `CyclicArc.exists_gapArcs` (b389a81cf, probe 0913-073424-67369).
- **Wiring.**
  - hT6's carrier Kazhdan/CCKWSystolicInvariantCliqueClosed (61eddb4a9) had never been queued; the lead queued it.
  - Also unrooted: TorsionFreeGreendlingerLeaf (queue line 501), TheoremCAssemblyGreendlingerLeaf (wave 9), OsinLemma94PlanarPieces and OsinLemma94DartMinimal (line 522), SimpleClosedWalkSides (line 520).
- **Other.**
  - cite-hull lands the Cor 7.4 piece statements now. jacobson, simple-group, hl-lemma46, fff-quotient and hull-component wait on the names.
  - nm-endpoints adds `#audit_closed_axioms` for `simpleUniqueTraceAtHypEmbedded_closed`.
  - dgo-analytic's lane report on main (09-12) still names hull-respell for SectionPocketCutInput. The roster names dgo-analytic, and dgo-analytic refreshes the report.

## Restart and rulings 09-13 ~08:30–09:10

- **Restart.** The coordinator process restarted at ~08:30. All 36 lanes were resumed with their current item in the resume message; none were lost.
- **Owners.**
  - OsinAppendixCutMerge (red on main since 09-12, omega at line 103) moves from hull-respell to hl-lemma46 for a proof-only repair. hull-respell's attempt is in the attic (a208f19a3). Nothing blocks on it now (see the disc collapse below).
  - The verifier fix in `scripts/check_non_mf_unconditional.py` stays with systolic-counts, whose calibration runs are under way. census re-runs verify-unconditional when it lands.
- **Lemma 9.4 over E.** hull-unbound's change is approved. GDSF labels are legal only over E := symmetricLabelAlphabet D, so PlanarPieces applies hmetric at (E, c+2) through `carrier_eq`, and CaseOne/CaseTwo take `WordConnectorPair E` (f2cc2be97). theoremc-retire restates CaseOneWalkStatement over E.
- **Lemma 9.4 respelling.** The statements are at 7a225d1d0 (Estimating/OsinLemma94ChainRespell), and `chainRespellInput_of_pieces` is proved.
  - CornerInsertionInput: simple-group.
  - PendantPathRemovalInput: jacobson.
  - SeparatingPathRemovalInput: hull-component, over GFaceMerge and the pendant removal.
- **Lemma 9.4 SideBudget.** `OsinLemma94PolygonCountInput.SideBudget` (∑ sideCount ≤ K·n, K before ε) is over-strong as stated. hull-count94 and audit-sec3 found this independently.
  - Pockets: a region side of length ≤ ε touching a cell s times leaves s unselected 2-sided G-faces, and DartMinimal keeps them.
  - Spurs: spaced backtracks of a quasi-geodesic ∂Δ split (A2) sides.
  - hull-unbound fixes the spelling. The two options:
    - F1: ∃K after ∀ε, with the antiparallel metric statement restated as ∃eps0 ∀eps ∀K ∃rho0, gated on sec5-sentences confirming that eps0 does not depend on K. Preferred.
    - F2: merged and pinch-split antecedents, with a weight_maximal carve-out.
  - The (A2) value-1 excursion skip is approved.
  - The fixed statement must be model-tested against both mechanisms, and must check whether `cuts.count` is bounded by n.
  - `Covers L` is true with L = 24ε, and hull-count94 builds it now.
- **LoopCut ruling (A), gate answers.**
  - Case 2 builds no new region candidate (sec5-sentences).
  - `ContiguityGeometry.ofSingletonFace`, `exists_quadrilateral_region` and the shared-edge producer can each force a same-cell competitor (hull-unbound, theoremc-retire), so (A) costs a refutation of Case 1 with i = j. For now that subcase stays a named hypothesis in theoremc-retire's OsinUnboundCaseOneFace.
  - Still waiting on audit-sec5 (does least area kill the same-cell quadrilateral?) and ghw-charp2's site census.
- **Lemma 9.3.** hull-euler's green assembly `phiPrimeCountInput_of_smallFaces` (Estimating/OsinAppendixEulerSmallFaces, 2279167e6, probe 0913-090235-64116) fixes the interfaces:
  - C4 `CornerFacesInput`: leavitt-units. Its parallel `CornerTwoGonInput` (d0a41c1da) is bridged or marked superseded.
  - C5 `CellFacesInput`: hs-vanishes. Its parallel `CellFaceCountInput` (bdd687708) likewise.
  - C6′ `SmallFaceHoldsInput`: debt-conditional.
  - Rule from here: the assembly owner states the piece Props and the producers prove them.
- **Closed.**
  - `EmptyTwoGonInput` has no hypotheses left: fff-periodic's `emptyTwoGonInput_holds` (2aa17abb0) collapses through `Surgery.InnerDiscRegion.ofPocketRegion` and `false_of_disc_collapse_singleton` (OsinPocketDiscMerge), so pinched pockets are covered. hull-select's zero-cell merge consumes the same contradiction.
  - `PocketRegionOfSimpleStatement` (dgo-analytic, c03054996, probe 0913-090829-84396) is closed over hull-component's `SimpleClosedWalkSides.sideFaces_boundaryCycle_eq` (d20913c51, probe 0913-090043-59913).
  - dgo-geometric's pinched two-gon model is green (4b78f0090, probe 0913-090336-67076). `no_faceSetBoundary` shows that FollowsBoundary routes cannot reach pinched pockets.
- **Pocket pieces.** They are restated in the ruled order, pinch, region, collar (a032ab802). The residual Props:
  - OsinSectionPocketFaceSetSectionStatement: kh-ejz;
  - PocketPinchStatement: hull-respell;
  - PocketCollarStatement: kh-torsion. It is the one double-collar construction, and hull-select's MultipleEdgeCut assembly consumes it.
  - PocketCell/OuterTransportStatement: go-lemma42, with sec2-sentences on two sub-pieces.
- **DGO Proposition 4.35.** `RelHyp.DGOProposition435PrintedStatement` is false as formalized: over G = ZMod 5, the forced base {t², t, t⁴} is not inversion-closed. baseline-debt lands `not_dgoProposition435PrintedStatement` in a new module, refuting the Lean spelling only. The `h435` consumers in GGT/DGOProposition435Printed are vacuous, and no census row names them.
- **Wiring.** Wave 8 is root green at 830b05464. Wave 9 (23 modules, build base 045b5f849) is building.
- **census merge 13** (9b413742b): 498 rows, 344 formalized; verify-unconditional 0 new; baseline 153 findings. 14 of the 18 open rows sit over hgreendlinger, and 7 unrooted carrier modules clear with wave 9.

## Rulings 09-13 ~09:10–09:40

- **Corrections to the ~08:30 section.**
  - "Nothing blocks on it now" about OsinAppendixCutMerge was wrong. OsinPocketDiscMerge imports it, so the EmptyTwoGon producers could not build until hl-lemma46's repair e7e55c0f2.
  - "EmptyTwoGonInput has no hypotheses left" was premature: its producer modules had not probed green. They have now: probe 0913-091627-32913 (base fd51edbc6) built OsinPocketDiscMerge and OsinPocketDiscEmptyTwoGon, and 0913-090831-85897 built the four SurgeryInnerDiscCollapse modules (da2d0b963, 2aa17abb0). `emptyTwoGonInput_holds` is closed.
  - "PocketCollarStatement: kh-torsion. It is the one double-collar construction" was wrong. The double collar is hl-lemma46's OsinPocketTwoCollars. kh-torsion proves GeodesicCollarStatement, which it consumes.
  - The C4/C5 spelling is reversed by hull-euler. The Lemma 9.3 assembly consumes the producers' `CornerTwoGonInput` (leavitt-units, d0a41c1da) and `CellFaceCountInput` (hs-vanishes, bdd687708), and drops CornerFacesInput, CellFacesInput and HoldsCellO. C6′ is restated as `TwoGonHoldsInput` (debt-conditional proves it). The assembly `phiPrimeCountInput_of_smallFaces` takes exactly C4, C5 and C6′ (hull-euler, 4beca2743, probe 0913-093143-91859).
- **LoopCut ruling (A) is FINAL.** `RespectsSections := target ≠ some source ∧ (target = none → ∃ j, TargetsSectionIndex cuts j a)`: a region from a cell to itself is not a candidate.
  - Why: with loops as candidates, LoopCutInput cannot be proved. audit-sec5's cap model (G = Perm (Fin 4), eps = 0, one relator) refutes it for that W. At eps ≥ 2, edge doublings force caps wherever two consecutive cell darts are unselected, so NoLoops would need a coverage claim far beyond Osin. (C) would rewrite EulerCount, Descent and the card clause.
  - Landing: ghw-charp2's census patches 01-09 (lane backup loopcensus/), rebased on origin bytes, one co-probe, one landing. The owners of the patched files hold edits until it lands. ghw-charp2 takes the ownerless SurgeryGFaceMergeRegions, OsinAppendixAssemblyPocket and SurgeryInnerGRegion.
  - Patch 07 keeps LoopCutInput and every hloop binder, and adds the closed producers `loopCutInput` and `osinLoopCutSection`. nm-endpoints then applies `osinLoopCutSection` at `_of_pocketParts`.
  - The cap counterexample is not landed in Lean (it compiles only against the old RespectsSections). audit-sec5 records it in its report.
  - Same-cell sites that (A) leaves without a competitor keep a named `hloop` binder:
    - OsinUnboundSharedEdge `false_of_digon_toward_cell` at i₂ = i: fff-periodic, new module.
    - The CaseOneFace/CaseOneRun one-cell connector pair: theoremc-retire, spelled A1 (premise kind target ≠ kind source in OsinLemma94CaseOneInput, one-cell pairs counted separately) or A2 (a polygon field). hull-unbound lands the PlanarPieces statement patch.
    - `false_of_quadrilateral_region` has no users, so its binder just stays.
    - audit-sec5 model-tests these subcases under OsinCCondition and LeastArea before the proofs go far.
- **Lemma 9.4.**
  - Case 1 needs only `OsinLemma94CaseOneWalkStatement` (theoremc-retire: 5be5cb6fc `osinLemma94CaseOneInput_of_walk`, 7f7ba2b4f `exists_quadrilateral_region_rotate` and `false_of_quadrilateral_face`, fd6ce3c09 over any E; probe 0913-091600-31828). ko-closed proves the walk Prop by list combinatorics (audit-sec3's route).
  - `SeparatingPathRemovalInput` is proved from `PendantPathRemovalInput` (hull-unbound, 7d4a2515f, probe 0913-093115-86638). ChainRespellInput now needs only CornerInsertionInput (simple-group) and PendantPathRemovalInput (jacobson).
  - PolygonRealization splits into: no two adjacent unselected G-faces (hull-unbound); no spur and quasi-geodesic cutting chains, through a word-metric respelling lemma (hull-component); the face partition (ghw-assembly).
  - Covers is closed: `osinLemma94PolygonCoversInput` with L = 24ε and rho0 = ⌈c/λ⌉ + 2 (hull-count94, 2b2e16cc6, probe 0913-093648-12289). The count residual is `OsinLemma94PolygonSideBudgetInput`.
  - SideBudget spelling: F1 is ruled. ∃K moves after ∀ε in the count Prop and the metric Prop, and (A2) sides skip value-one excursions. hull-count94 writes the Rule 22 change to PlanarPieces, the metric Prop and CaseOneWalk as one co-probed landing, and confirms with sec5-sentences that eps0 does not depend on K. The owners hold edits until it lands, and theoremc-retire's A1 patch rebases after it.
  - Region-side count `sum_card_regionFacingUnbound_le` for hull-count94 (audit-intro, 9d3013e41, probe 0913-091959-40244). Covers must leave no directly shared cell-cell edge.
- **Pocket pieces.**
  - PocketPinchStatement reduces to `PocketPinchPinchedStatement` (kh-cckw, 33951a5b6, probe 0913-091746-34826, with hull-respell).
  - OsinPocketTwoCollars (hl-lemma46, 282e3a821, now 7eb17a3e9, probe 0913-092959-67901). `exists_twoCollars_of_ne_or` allows an empty arc when some arc is nonempty or some side value ≠ 1.
  - `PocketCollarStatement` takes `PocketCarrier.Nondegenerate`, and the assembly proves it from least area (dgo-analytic, b34e788e8, probe 0913-093324-3872). The degenerate carrier is gone, and no new Prop is open.
  - Pocket-region boundary cycles are simple closed walks under FollowsBoundary (hull-bridge for kh-torsion, 87715ad6e, probe 0913-091940-39141).
  - FollowsBoundary: hull-euler keeps EmptyTwoGonInput unchanged, and the consumer supplies the walk.
- **hgreendlinger.** Ten census rows cite TorsionFreeGreendlingerLeaf (nm-endpoints, 7d2a5b28d), with hgreendlinger their only residual. Its root producer `_of_pocketParts` takes OsinLemma94SectionStatement, OsinMultipleEdgeCutSectionStatement, OsinLoopCutSectionStatement, OsinPhiPrimeCountSectionStatement and OsinSectionPocketCutSectionStatement.
- **Census and wiring.** root-wire's 559636b4a root-imported the carrier modules. census merge 15 (de0c922ef) has 498 rows: formalized 345, partial 17; verify-unconditional 0 new; baseline 153. No row says "carrier not root-reachable".
- **Assignments.** hl-lemma46: census of the open W1 leaf Props with owners (drafts/w1-leaves-0913.md), then the first unowned leaf. hull-component: the word-metric respelling lemma. fff-periodic: the SharedEdge same-cell case.

## Rulings 09-13 ~09:40–10:20

- **SectionPocketFaceSetInput: ruling (B).** The output moves to an O-equivalent copy: `∃ X', Nonempty (OEquivalentDiscDiagram S.diagram X') ∧ Nonempty (PocketFaceSet D eps X' lo hi)`.
  - Why: on S.diagram a pocket walk can contain both darts of one edge, and then no face set has that walk as its boundary. kh-ejz found three ways:
    - (a) A section backtrack between the two targets, allowed once c ≥ 2λ. It is a spur with the outer face on both sides.
    - (b) An edge of the gap arc with cell i on both sides.
    - (c) x.right sharing an edge with y.left. The manuscript's Γ₁ avoids this.
  - The pinch and collar Props already output on O-equivalent copies (OsinPocketPieces:236, :257), so the assembly composes one more equivalence.
  - Landing: kh-ejz lands the restatement together with dgo-analytic's assembly change (Rule 22). MultipleEdgePocketRegionInput takes the same form if it needs it, and hull-select's MultipleEdgeCut assembly composes the extra equivalence.
  - Pieces:
    - P2′, the sides theorem for closed walks that touch but never cross: kh-ejz, model-tested by audit-sec3.
    - For (a), thickening an outer spur into a G-digon: hs-vanishes.
    - For (b), SurgeryFaceEdgeDoubling on cell i's face, if it applies.
    - hkept comes from `zeroCellPocketMerge` (hull-select, ce1028aa1, probe 0913-094902-38721).
- **SideBudget.** Moving ∃K after ∀ε does not repair the Prop on its own. The essential part of F1 is (A2): no splits at value-one excursions.
  - audit-sec3's instance: G = Z, alphabet {±1, ±2}, λ = 1/2, c = 3, one G-face with walk 2^(3t) (-1)^(6t) and t outward spurs "1 -1" on its 2-side. The boundary side splits t times at every eps, rho and n.
  - hull-count94 lands (A2) together with the K move.
- **Lemma 9.3.**
  - C5 is proved: `cellFaceCountInput` (hs-vanishes, a6a2cadda, probe 0913-100213-68371; recorded by hull-euler in e84468da9). PhiPrimeCountInput now needs only C4 `CornerTwoGonInput` (leavitt-units) and C6′ `TwoGonHoldsInput` (debt-conditional).
  - Wiring: hull-euler's chain is at queue lines 572–579 and ExteriorCellFaces at line 589. OsinAppendixEulerCornerTwoGon (d0a41c1da) is not queued; root-wire was told to include it.
- **Lemma 9.4.**
  - Case 1:
    - `osinLemma94CaseOneWalk : OsinLemma94CaseOneWalkStatement` (ko-closed, eb9010962 and 8f0f73966, probe 0913-095509-55850).
    - `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk` proves OsinLemma94CaseOneInput. theoremc-retire lands the composed endpoint.
    - audit-sec3: OsinLemma94CaseOneSameCellStatement is redundant, since `false_of_quadrilateral_face` and `osinLemma94CaseOne_false_of_walk` carry no kind hypothesis.
  - Polygon realization: `osinLemma94PolygonRealizationInput_of_pieces` and `gFacesApart_of_dartMinimal` (hull-unbound, 1130c8dbc, probe 0913-095511-56070). Residuals and owners:
    - OsinLemma94CuttingChainsInput: hull-unbound, from ChainRespellInput, PendantPathRemovalInput and QuasiGeodesicRespellInput.
    - OsinLemma94CellArcsInput: ko-closed.
    - OsinLemma94BoundaryArcsInput: cite-hull.
    - OsinLemma94PolygonPartitionInput: ghw-assembly.
  - Case 2 transports: insertion (sec2-sentences, c652fa749) and spike deletion (sec5-sentences, 14daf9b00, 31982031d, 0838416d4, ba4233ef8).
  - audit-sec3's model tests:
    - CornerInsertionInput and PendantPathRemovalInput have no counterexample.
    - The C-condition line model is on main (594d1e97a): a model of OsinCCondition on the line at every eps and rho.
- **Pocket pieces.**
  - `pocketCollarStatement_of_geodesicCollar` (dgo-analytic, 6cb3014e6, probe 0913-100702-85407).
  - kh-torsion builds GeodesicCollarStatement from a strip face: insert g across the strip, and for g = [] join the two ends at a vertex (hull-bridge). The monogon s = [d] needs fff-quotient's same-corner doubling.
  - hull-select next: `multipleEdgeCutInput_of_pieces` (OsinPocketMultipleEdgeAssembly), over hl-lemma46's OsinPocketMultipleEdgeTransport (1d177113c).
- **Hull corollaries.** `printedHullCorollary73_of_greendlinger` (cite-hull, 477777a5e). Corollary 7.3 now takes only the Greendlinger wall, as Corollary 7.4 already did.
- **Wiring.** Wave 9 (559636b4a) is confirmed on origin: 23 modules, closure 6351, 0 dangling imports. Wave 10 sweeps from queue line 534, with 36 modules plus CornerTwoGon.
- **Resumed lanes.** root-wire, systolic-counts and cite-hull had MSI jobs finish while they were stopped, and each was resumed once. systolic-counts' verifier run exited VERIFY_NEW=1, and the lane is triaging it.
- **Assignments.**
  - fff-quotient: the same-corner doubling.
  - hs-vanishes: the outer spur thickening.
  - ko-closed: CellArcsInput.
  - cite-hull: BoundaryArcsInput.
  - audit-sec3: model-test C4 and C6′, then P2′.

## Rulings 09-13 ~10:20–13:05

- **Wiring.**
  - Wave 10 is ROOT GREEN at 65d0a4497 (39 modules).
  - Wave 11 is ROOT GREEN at 9eba4d854 (5 modules: CyclicArcSub, OsinLemma94PendantRemoval, HullLemma35PieceWords, OsinPocketGlueDiagram, OsinPocketMultipleEdgeTransport).
  - After wave 10 every census carrier module is root-reachable.
  - OEquivalentCellFaces was held after a failed probe. sec2-sentences' re-probe is green, and its queue entry is at line 631.
  - Wave 12 sweeps from queue line 606.
  - simple-group's DiscEmbeddingAwayUnbound rewrite (f7538e223) removes the `DiscEmbeddingAway.regionCandidate_*` declarations that clashed with sec2-sentences' OsinLemma94InsertionTransport (c652fa749), so both modules can be wired.
- **Census.** Merge 17 (d0aba6104) has 498 rows: 345 formalized, 17 partial, 146 baseline active. Merge 18, the first under systolic-counts' verifier fix (736f7ea44), stopped on two unclassified inline limit-set findings. CI "Sentence-level census" stays red until merge 19.
- **Pocket pinch.**
  - PocketRegion admits pinched pockets (dgo-geometric, 26f3e086e). The route A disc collapse needs neither FollowsBoundary nor a simple walk (4894cfceb).
  - hull-respell's obstructions (615da4f77) are A, a notch, and B, a lake. The smallest instance of each has an O-equivalent refill.
  - Ruling:
    - R2 (drop inner FollowsBoundary) if kh-torsion confirms no collar stage uses it, else R1.
    - B stays a residual under both.
    - dgo-geometric model-tests A and B.
    - The label binder (hlabel) is accepted.
  - dgo-analytic:
    - Ruling (B) landed at bdc7337fd: the face set lives on an O-equivalent copy with legal labels, with PocketPinchLabelledStatement.
    - cb0ec2d30 adds PocketFaceSet.ClosedWalk, a chain that closes and may repeat vertices. SectionPocketFaceSetInput now ends with ∃ K, K.ClosedWalk.
    - kh-ejz's unlanded PocketWalk.toPocketFaceSetOfNoncrossing supplies that conjunct.
  - Under R2, Simple is IsNoncrossingClosedWalk (kh-ejz, 26a7858f2) plus FollowsBoundary of the outer cycle (dgo-analytic).
    - At a touching vertex, A breaks the inner cycle and B breaks the outer one. So A needs no pinch, and B stays in the pinch Prop.
    - The transports and `nonempty_osinSectionPocketCut` need the outer cycle to follow the boundary.
    - New lemma: PocketRegion.inner is an IsDiscRegion, through `toDiscRegion_of_euler`. dgo-analytic owns it and may hand it to hull-euler.
  - kh-cckw proved the case where both cycles follow the boundary (OsinPocketUnpinchedEuler, 74d4ebd34). PocketPinchPinchedStatement stays open (hull-respell with kh-cckw).
- **LoopCut (A) sites.**
  - audit-sec5's cap counterexample is landed (LoopCutCapCounterexample, 0c7a92957, over S₃ with W = y y y), correcting line 587. It will be rewritten for the post-(A) definitions, not deleted, and it joins ghw-charp2's co-probe.
  - ghw-charp2's census (84cf5432c) swept 45 files and found no new sites.
  - Patches 01-10 land as one co-probe in audit-sec5's form: SameLoopProfile is a separate Prop next to SameTargetProfile.
  - Patch 10(f) is overruled. `osinLemma94CaseOneInput_of_walk` stays and gains an OsinLemma94CaseOneSameCellStatement binder.
  - Correction to line 634: OsinLemma94CaseOneSameCellStatement is not redundant after patch 09(d).
  - Site 5 (PolygonCovers at j = i) goes to fff-periodic under option (a).
    - Covers takes a factor ⌈1/λ⌉ on the sides, and L depends on λ and c.
    - fff-periodic proves case (T), where C2 has no relator cell.
    - Case (C) is a named binder owned by fff-periodic. It can be discharged from the threaded OsinLemma97Below.
    - It is co-probed with hull-count94. `dense_of_covers` absorbs the factor (density at ρ/(4K²)).
  - Site 6: ZeroCellPocketMergeStatement gains `target ≠ some source`.
- **Lemma 9.4.**
  - F1 landed (hull-count94, 9f8779c4e).
  - SideBudget Stage B:
    - Sum only over polygons with an (A1) side, since a bubble model refutes the unfiltered sum.
    - Minimality is (darts, faces) lexicographic, pending audit-intro's check.
    - Sides stay contiguous, and the budget counts skip-arc classes.
    - hull-component takes a sub-piece from hull-count94.
  - One-cell connector pair: A1 accepted, A2 false.
    - Option (i): OsinLemma94SectionStatement and UnboundInput gain `OsinLemma97Below … Delta.rCellCount`.
    - PlanarPieces gains OsinLemma94CaseOneOneCellInput, which concludes `Nonempty (OsinLoopCut …)`.
    - Landing order: (A), then F1, then theoremc-retire's threading.
    - ko-closed writes case (a) and the OsinLoopCut construction.
    - The tex does not print Lemma 9.4; it cites Hull.
  - Realization pieces closed:
    - CellArcsInput (ko-closed, 5e5a98049), BoundaryArcsInput (cite-hull, 1b453429f) and QuasiGeodesicRespellInput (hull-component, 6b5a1f7d1).
    - Both inputs of ChainRespellInput: CornerInsertionInput (simple-group, f7538e223) and PendantPathRemovalInput (61c2ade8e).
  - Face partition (PolygonPartitionInput):
    - ghw-assembly landed OsinLemma94PolygonLists (269a91ab3) and OsinLemma94PolygonKinds (5c69ca42d). OsinLemma94PolygonSides is in flight; its last probe failed.
    - cite-hull proposes to take P.Maximal in OsinLemma94PolygonMaximal, over PolygonKinds only.
    - Open: the face enumeration, the walk and cutting_interior fields, and the assembly.
  - Case 2 does not use ChainRespellInput.
    - SpikeTransport (ba4233ef8) and SeparatedCornerInsertionInput (b52230097) are on main.
    - sec2-sentences proves `separatedCornerInsertionInput` in OsinLemma94SeparatedInsertionProof (619b70139, unverified), over OsinLemma94CornerInsertion's helpers. simple-group does not duplicate it.
- **Pocket pieces.**
  - `osinMultipleEdgeCutSection_of_pieces` (hull-select, 2db85602c) takes three binders: OsinMultipleEdgePocketRegionSectionStatement (kh-ejz), GeodesicCollarStatement (kh-torsion) and PocketCellTransportStatement (go-lemma42).
  - kh-torsion's SurgeryGeodesicCollarAssembly (a89b55a0d) reduces GeodesicCollarStatement to StripStatement, InsertStatement and JoinStatement.
    - Landed so far: the corner join (hull-bridge, e7fa1c6ab, 336c80ccc) and the monogon doubling (fff-quotient, 75d0892a2).
    - kh-torsion keeps Strip, hull-bridge has Join, and simple-group takes Insert.
  - go-lemma42's glue chain ends at f914f8728 and is wired through OsinPocketGlueDiagram. hl-lemma46's multiple-edge transport (1d177113c) is wired.
- **Lemma 9.3.** hull-euler landed `osinPhiPrimeCountSection_of_pieces` (OsinAppendixEulerSection, 6401c70a6, green, queue lines 626–627).
  - Its two binders are OsinCornerTwoGonSectionStatement (C4, leavitt-units) and OsinTwoGonHoldsSectionStatement (C6′, debt-conditional).
  - C5 is filled by `cellFaceCountInput`.
- **Hull Lemma 3.5 is closed** (baseline-debt).
  - `printedHullLemma35 : PrintedHullLemma35` (HullLemma35Closed, b5f91627e) holds for all n, all m_i and every universe, with axioms [propext, Classical.choice, Quot.sound].
  - Pieces: 5acca195c, 28fbaaffe, 6dd556d61, 7401027ce, 1369b2bed, 520f03021, 0efcdd55c.
  - Census row LINE:1682 is at 711c053f1. HullLemma35Letter and HullLemma35Closed are queued for wiring.
- **Endpoints.** nm-endpoints' report (e3e3dda23) lists the four open Greendlinger slots and their leaf Props. nm-endpoints waits for ghw-charp2's patch 07, then lands `relativeGreendlingerQuasiGeodesicLeastArea_of_loopClosed`.
- **Off-route blockers.** systolic-counts writes the list of census carriers to flip where an off-route Prop blocks them.
- **Assignments.**
  - hull-euler: the inner-region Euler lemma, if dgo-analytic hands it over; then the PhiPrimeCount closure once C4 and C6′ land.
  - hl-lemma46: one piece of PocketCellTransportStatement (go-lemma42) or PocketOuterTransportStatement (hull-select).
  - baseline-debt: the largest group of census baseline findings that no lane owns.
  - simple-group: InsertStatement.
  - hull-component: a Stage B sub-piece from hull-count94.
  - cite-hull: P.Maximal, once ghw-assembly agrees.
  - ko-closed: the one-cell Case 1 module.
  - dgo-analytic: the R2 restatement co-probe.
  - dgo-geometric: model tests of A and B.
  - systolic-counts: the off-route flip list.

## Rulings 09-13 ~13:05–13:40

- **Closed.**
  - Lemma 9.4 Case 2: `osinLemma94CaseTwoInput` (sec5-sentences, OsinLemma94CaseTwo, e0e94015d, green), over `separatedCornerInsertionInput` (sec2-sentences, 619b70139, green).
  - C4: `cornerTwoGonInput` (90245333d) and `osinCornerTwoGonSection` (0c42391c2), leavitt-units. hull-euler checked both against main. The Lemma 9.3 section now waits only on C6′, OsinTwoGonHoldsSectionStatement.
  - Face partition: `osinLemma94PolygonPartitionInput` (ghw-assembly, OsinLemma94PolygonPartition, 746028b24, green), over PolygonLists 269a91ab3, PolygonKinds 5c69ca42d, PolygonSides a76186267 and PolygonMaximal 9f03bfcd3.
    - `osinLemma94Section_of_residuals` (hull-unbound, 0087a5095) now has two open hypotheses: OsinLemma94PolygonCountInput and OsinLemma94CaseOneInput.
  - Collar join: `GeodesicCollar.joinStatement` (hull-bridge, SurgeryGeodesicCollarJoin, ce39bca65, green).
  - Monogon strip: `MonogonDoubling.monogonStrip : MonogonStripStatement` (fff-quotient, SurgeryMonogonDoublingStrip, a46e7beda, green). It is StripStatement at s = [d], without the IsSimpleClosedWalk hypothesis.
  - `CellPocketWalk.exists_of_joinsCells` (jacobson, OsinPocketCellWalk, 65e5e758c, green): the pocket walk of two regions joining the same two cells.
  - kh-ejz: NoncrossingClosedWalkSides (26a7858f2; 37957f19b, the pinched two-gon pocket is a noncrossing closed walk; aa2df0eaa, the pocket face set in walk order).
  - C6′ module 1: OsinAppendixEulerTwoGonLabels (debt-conditional, 81cb719d3).
  - `RelHyp.not_dgoProposition435PrintedStatement` (baseline-debt, DGOProposition435PrintedCounterexample, 7976a7ca7, green).
    - It refutes the Lean spelling, not DGO's printed Proposition 4.35: the forced base is not inversion-closed.
    - Its three `h435` consumers in DGOProposition435Printed are vacuous, and none is a carrier.
- **Wiring.** Wave 12 is ROOT GREEN (LANDED ROOT 141bea9e6, five modules). Wave 13 is in pre-flight over queue lines 613–647.
- **R2 Simple and the Euler lemma.**
  - IsNoncrossingClosedWalk alone is too weak (hull-euler, checked by dgo-analytic). A three-petal rose passes every field, because `turn_mem` forbids crossing only at vertices passed twice, and reclosing gives χ = 0.
  - With outer FollowsBoundary the Euler lemma holds, so that conjunct of R2's `Simple` is load-bearing. hull-euler has the lemma in that form.
  - The "never crosses" docstring of NoncrossingClosedWalkSides is wrong at vertices passed three or more times. kh-ejz has been told.
- **R1 against R2: still open.**
  - fff-quotient, splitting with kh-torsion, either ports StripStatement from IsSimpleClosedWalk to noncrossing plus outer FollowsBoundary, or finds the configuration where the port fails.
  - hull-bridge takes a Strip sub-module (Double or Pinch) from kh-torsion.
  - InsertStatement stays with simple-group, overriding kh-torsion's handoff to hull-bridge.
- **Pocket circuit identification.**
  - kh-ejz: the turning condition for K.walk is not local. It reduces to identifying the `FaceSetCircuits.boundaryPerm` circuit through a gap dart with the pocket's complement cycle: x.left, the gap on Π_i, y.right, then the ∂X gap reversed.
  - Nothing on main produces that identification, or the single-circuit hypothesis `hall` of `FaceSetCircuits.toDiscRegion`.
  - kh-ejz owns the Prop. It checks first whether the Prop is the producer of R2's `Simple` for the pocket walk, then model-tests it on OsinPocketPinchedTwoGonModel. cite-hull co-proves it.
  - Case (d) is a cell-i edge on ∂X that lies in both gaps. If the model realizes it, it goes to hs-vanishes together with (a). If planarity excludes it, the exclusion goes inside the identification Prop.
- **Case 1, one-cell pairs.**
  - OsinLemma94CaseOneSameCellStatement (OsinUnboundCaseOneFace:466) has no OsinLemma97Below binder. As spelled it is as hard as Lemma 9.7 on smaller diagrams, so no lane proves that spelling.
  - ko-closed's Shape 1: a spur x x⁻¹ of Π's boundary sits at the junction of two consecutive sides, and the pocket is empty. NoLoops, GFacesApart and DartMinimal all hold and no OsinLoopCut exists, so case (a) does not follow from them.
  - Ruling: option (2). The metric Prop delivers one-cell pairs at λ⁻¹(ε + c), and ko-closed proves (a) by the value argument. This is gated on the metric owners confirming F1's quantifier order.
  - The fallback, option (1) (count one-cell pairs separately), needs a new ruling together with hull-count94.
  - (b) needs the X-pocket as a PocketRegion plus a collar. jacobson offers ko-closed the collar step.
- **SideBudget and Covers** (audit-intro's pinched-cell model: n = 1, λ = 1/8, c = 3, relator g_1·abc·…·g_{t+1} with abc = 1).
  - The patched budget passes, with two spelling points. A class is a maximal run of consecutive `.cell j` sides whose gaps have listVal 1. A one-sided bubble is a polygon with exactly one class, of kind (A1).
  - Covers fails when the class word concatenates P's side words, since the 3t bubble darts stay unbound.
  - Ruling: the class word is `dartWord` of the reversed cell arc, gaps included, and L = 24ε + 2(K+24)⌈(c+2)/λ⌉, fixed after K. The Covers producer (2b2e16cc6) is respelled in the same co-probed landing.
  - Case 1 users accept a connector endpoint on a gap dart. Nobody builds the un-pinch surgery unless theoremc-retire or ko-closed shows that a user cannot accept it.
- **Pinch.**
  - dgo-geometric's lobe fixture (OsinPocketPinchedTwoGonLobe, 4181011af, green) shows that PocketPinchPinchedStatement ties K' to K only through D, eps, lo and hi. So the lobe with X' = X satisfies it, which matches hull-respell's lobe selection.
  - The wrap case is the one pinch residual with no planned proof.
- **Assignments.**
  - fff-quotient: the noncrossing StripStatement, with kh-torsion.
  - hull-bridge: a Strip sub-module from kh-torsion.
  - cite-hull: the pocket circuit identification, with kh-ejz.
  - sec5-sentences: OsinLemma94PolygonCountInput, with hull-count94.
  - baseline-debt: C6′, with debt-conditional.
  - ghw-assembly: the wrap case, with dgo-geometric and hull-respell.
  - dgo-geometric: model the wrap case.
  - ko-closed: case (a) by the value argument, after the threshold gate.
  - jacobson: the (b) collar step, if ko-closed agrees.
  - root-wire: wave 13.

## Rulings 09-13 ~13:40–13:46

- Lemma 9.4 realization: OsinLemma94PolygonRealizationInput is CLOSED.
  - hull-unbound 409bbbf72 (Case 2, probe 0913-131745-36741) and 4002b9371 (partition, probe 0913-133025-35313), module OsinLemma94SectionResiduals.
  - `osinLemma94Section_of_residuals` takes only PolygonCountInput and CaseOneInput.
- Wave 13 (root-wire): building, tag 0913-133632-59092, base 03f8f2c88, 30 modules.
  - Includes the partition chain: PolygonLists, Kinds, Sides, Maximal, Partition, then SectionResiduals at 4002b9371.
- Patch 10(f) is overruled.
  - `osinLemma94CaseOneInput_of_walk` stays and takes a same-cell binder after (A).
  - hull-unbound does not compose it today; the section closes over the option (2) spelling.
- Option (2) Dense respelling: hull-unbound drafts it in OsinLemma94Pieces.
  - A one-cell conjunct at λ⁻¹(ε + c), inside the F1 order ∀ λ c, ∃ ε₀, ∀ ε ≥ ε₀, ∀ K, ∃ ρ₀.
  - Gated on sec5-sentences (the proof delivers it) and ko-closed (case (a) consumes it).
  - Co-probed with AntiparallelMetric, PlanarPieces and SectionResiduals. Fallback (1) if the proof cannot deliver.
- R2 Euler lemma: hull-euler builds NoncrossingClosedWalkEuler.
  - `IsNoncrossingClosedWalk.reclosed_euler`, with outer following as a hypothesis, and `toDiscRegion_of_euler`.
  - The three-petal rose is the model test.
  - It does not wait on C6′.
- R2 pocket region: dgo-analytic drafts the noncrossing-walk region builder over hull-euler's signature and lands it unwired.
  - The Simple / PocketRegionOfSimple / PocketCarrier / collar co-probe waits for a green Euler lemma and no port failure from fff-quotient.
- C6′ pinched-walk case: debt-conditional carries PocketPinchStatement, the existing hpocket binder (hull-respell's piece, reduced by kh-cckw). No new Prop.
- audit-sec3 truth audit of the residuals:
  - PartitionInput and CaseTwoInput are true and proved.
  - Wrap-pair fidelity note: Maximal skips (sideCount − 1, 0), and baseOf does not rotate to a turn, so a run can split at the base, at most one extra side per polygon. Routed to hull-count94, audit-intro (take the SideBudget class cyclically or add one class per polygon to L) and theoremc-retire.
  - Card bound: no fixture; the induction discharges it (osinLemma97_atParameters_of_inputs).
- Census, merge 17 (baseline-debt): no residual Prop outside W1.
  - baseline-debt re-grades the cite-ejz LINE:1145 row itself; sec5-sentences re-grades LINE:1629.
  - baseline-debt then takes the unowned flip-list docstrings (nm-endpoints report ~236–245, Assembly.lean:818).
- nm-endpoints cf3c78b35: 16 flip-list docstrings marked, probe 0913-133143-40961; report 3acae2f1d re-checks the residuals at bf7d5994b.
- audit-sec5 same-cell model test. (A) survives and does not force (C).
  - (1) No R-cell in the pocket H: metric kill false_of_sameCell_connector_of_noCells.
    - Morse radius κ; ε < κ + (2κ + c′)/(2λ).
    - No DartMinimal, Maximal or least area.
  - (2) An R-cell in H: nonempty_osinLoopCut_of_sameCell_connector from ofParts, ofSimpleClosedWalk and diagram_leastAreaCut.
    - Needs OsinLemma97Below (option (i) threading).
  - Gap: a folded spur at the junction defeats theoremc-retire's DartMinimal/PendantPathRemoval/Maximal route for case (a).
  - Site (i): false_of_digon_toward_cell at i₂ = i is false as printed. Option (a) stands, and binder (C) discharges from hbelow.
  - Forwarded to ko-closed to decide:
    - (1) versus the λ⁻¹(ε+c) respelling, which may cancel hull-unbound's draft;
    - (2) versus jacobson's collar step;
    - whether audit-sec5 writes (1).
- LoopCutCapCounterexample (0c7a92957, unwired): audit-sec5 writes the post-(A) rewrite in place for ghw-charp2's co-probe. No attic move.
- hull-count94 Stage B, module OsinLemma94PolygonClasses: ClassBudget over polygons with an (A1) class and ≥ 2 classes; ClassCovers with L = 24ε + 2(K+24)⌈(c+2)/λ⌉.
  - Helpers: audit-intro (short-side count ≤ 2ε|M|), sec5-sentences (ClassBudget from the 9.3 run counts), hull-component (gap-length lemma, bubble accounting).
- Ruling: CaseOneInput and CaseOneWalk take pairs on class words, gaps included (roster l.786).
  - The Rule 22 change folds into one co-probe with hull-unbound's Dense respelling, after ghw-charp2's (A) co-probe.
- Opening surgeries: not built yet (l.786 stands). hull-count94's finding: no FaceSetBoundary region contains a hair or a bubble.
  - Goes to ko-closed and theoremc-retire.
  - If a user needs a region containing a gap: hair opening goes to hs-vanishes (extends (a); against weight_maximal), bubble un-pinch goes to leavitt-units (over hull-respell's vertex explosion).
- systolic-counts flip list 20d0ec06d: 48 flip, 37 superseded, 1 keep; 11 of the 86 are vacuous at {0,0,0}.
  - The embedded bridge's closed theorem states an implication with the LA-certificate antecedent; the verifier flags it buried-conditional. The antecedent is the hgreendlinger slot.
  - Census: 307/366 clear under LA.
- hull-respell 24ff94312 (OsinPocketClosedWalkNoncrossing, probe 0913-133554-56930): every pocket face set in walk order is IsNoncrossingClosedWalk.
  - Under R2, K.Simple = K.ClosedWalk + outer FollowsBoundary, and the R2 pinch only absorbs lakes and re-pairs side darts.
  - B (source in a lake) stays inside PocketPinchLabelledStatement.
- debt-conditional C6′: module 1 81cb719d3 green; module 2 OsinAppendixEulerTwoGonFaceClass ee96efa9d, probing.
  - Ruling: no new pinched-walk Prop. The two-gon pocket walk has the section pocket shape, so module 4 consumes kh-ejz's O-equivalent face set, then PocketPinchLabelledStatement, then ofSimpleClosedWalk and EmptyTwoGon.
  - The pinch statement must cover that pocket.

## Rulings 09-13 ~14:00–14:01

- Roster 0da58be4b records the 13:40–14:00 rulings.
- InsertStatement: simple-group and hull-bridge both claimed it about 13 seconds apart, after kh-torsion re-offered it to hull-bridge.
  - Ruled (third time): Insert stays with simple-group.
  - hull-bridge sends any draft to simple-group and takes a Strip sub-module (Double or Pinch) from kh-torsion, stated in fff-quotient's port form.
- hl-lemma46 takes PocketOuterTransportStatement (OsinPocketPieces:332) outright; hull-select is blocked on the co-probe and sends any draft.
  - go-lemma42 keeps PocketCellTransportStatement.
- leavitt-units stops waiting on the copies (b) and (c): the output is ruling (B)'s O-equivalent copy, with the doubled edges gone.
  - It consumes or writes the FaceEdgeDoubling dart transport and model-tests first. This comes ahead of the gated bubble un-pinch.
- Pocket circuit identification: REFUTED by kh-ejz.
  - A pinch of x makes the boundaryPerm circuit mix C_P and C_Q; a lake makes the gap circuit bound only P1. K.walk is still noncrossing.
  - Replacement, the parity route:
    - (A') a nodup closed walk equal to ∂U is noncrossing, with no planarity;
    - (B) a Z/2 face colouring on planar maps, col(face α d) ≠ col(face d) ↔ walkKeep, by strong induction splitting at a repeated vertex;
    - (C) col is constant on x and y, so the walk darts carry colour c0;
    - (D) U = {col = c0} has ∂U = K.walk, then toPocketFaceSetOfNoncrossing.
  - Residuals: (iii') nodup + alpha_not_mem of K.walk on the copy (the copies (a) hs-vanishes, (b)/(c) leavitt-units) and (ii) kept ∈ U.
  - Rulings:
    - kh-ejz builds (B), (C), (D) in a new module, not NoncrossingClosedWalkSides (three landed importers). It model-tests (C) on the pinched two-gon model and the lake complement.
    - (A') is not rebuilt: check hull-respell's BoundaryCycle.isNoncrossingClosedWalk (24ff94312) first. cite-hull's FaceSetCircuitNoncrossing (i) is the same claim; its (ii) is dropped unless (D) uses it. cite-hull may take (C) from kh-ejz.
    - Q1: hs-vanishes' thickening is stated at 0a7715b56.
    - Q2: dgo-analytic states the zero-cell merge on the copy (SectionPocketCutInput, l.405, l.617).
- Wave 13 ROOT GREEN, LANDED ROOT e0dcf8b99 (13:51, 30 modules, partition chain + SectionResiduals + CollarJoin). Wave 14 from the queue: GlueOuterArc, GlueOuterTransport, QuasiGeodesicValueOneGap, ShortSides, FaceSetCircuitNoncrossing.
- PocketOuterTransportStatement CLOSED by hull-select: `pocketOuterTransport` 71d59592c over OsinPocketGlueOuterArc 4a4f1a6b6 (probes 0913-134953-22063, 0913-134755-12194), using only go-lemma42's glue interface. hl-lemma46's assignment is void.
  - Free lanes hull-select and hl-lemma46: go-lemma42 names at most two disjoint sub-pieces of PocketCellTransportStatement, one per lane.
- `hin` finding (hull-select): the assembly feeds inner FollowsBoundary to exists_twoCollars_of_ne_or → GeodesicCollarStatement (SurgeryGeodesicCollar:71), which also returns inner FollowsBoundary.
  - dgo-geometric e533e5581 (green, unwired, OsinPocketPinchedTwoGonOuterFollows): in Configuration A the inner cycle fails and the outer follows; pinchedK satisfies R2 Simple, so this pocket needs no pinch.
  - So under R2 the collar must be restated over the outer spelling. kh-torsion decides R1/R2 with this.
  - dgo-geometric corrects C3–C6: all proved (exterior_of_isTwoGon, cornerTwoGonInput 90245333d, cellFaceCountInput, emptyTwoGonInput_holds 2aa17abb0); only C6′ is a stated input. Configuration B (two-petal rose) is next.
- kh-torsion: Walk 5197fa6fc landed; stripSingleton (Double) probing. Corrected: Insert stays with simple-group (fourth notice); Join is on main at ce39bca65. hull-bridge takes ONE Strip sub-module (pinch step or induction).
- cite-hull 67ec49f02 FaceSetCircuitNoncrossing: isNoncrossingClosedWalk_of_isChain_boundaryWalk = (A'), no planarity. Middle-walk chain lemmas over C = x ∪ y ∪ {Π_i, outer} are held (the refuted claim); chain lemmas only against kh-ejz's U.
- Lemma 9.4 side budget:
  - short sides ≤ 2ε|M| landed by sec5-sentences 4b6dd3cd8 (OsinLemma94ShortSides; audit-intro's duplicate avoided);
  - gap lemma hull-component a3169d05f (QuasiGeodesicValueOneGap).
  - sec5-sentences finding: nothing on main gives #A1 + #A2 ≤ 2|M| + n + r at diagram level (typeA12_le and RunInput carry it as fields).
  - Ruled: sec5-sentences writes the diagram-level class-transition count over realized polygons; hull-count94 writes the respelling in PolygonClasses and consumes it.
  - hull-component's BudgetFilter lands only if hull-count94 consumes it. audit-intro and hull-component wait on the PolygonClasses names.
- C6′ module 4 (baseline-debt): SectionPocketFaceSetInput gives a copy with a kept cell, while EmptyTwoGonInput needs a relator-free region on S.diagram.
  - Ruled: module 4 targets an O-equivalent copy, with a transport lemma for the empty-two-gon conclusion; check first that the conclusion is O-invariant.
  - The merge (dgo-analytic) is also on a copy. debt-conditional keeps the direct plan for the noncrossing, non-leaking case.
- ghw-charp2 (A) co-probe: approved to co-land leavitt-units' OsinAppendixEulerCornerTwoGonCount one-line fix at l.497, with an origin-blob check at push. LoopCutCapCounterexample is probed without; audit-sec5 rewrites after (A) lands.
- theoremc-retire, option (i) threading T (draft $NM/backup/theoremc-retire/threading-option-i-draft.lean.txt, base c8bd88c14, unprobed): OsinLemma97Below binder through Sections, SectionInduction, DescentInduction, Assembly, Lemma97Pocket, Counting, Pieces, PlanarPieces.
  - Ruled: T lands only if ko-closed picks (2), the R-cell case that needs hbelow. It then runs as one co-probed landing after (A), folded with hull-unbound's Dense respelling (same Pieces/PlanarPieces files), with hold notices and origin-blob checks. theoremc-retire adds the unowned Assembly and Lemma97Pocket to its files.
  - OC6 Run patch rides in ghw-charp2's (A).
  - Gap finding (l.786/849): false_of_quadrilateral_face needs the reversed source arc as a literal piece of f's walk, so pairs whose [a,a'] or [b',b] strictly contains a gap (bubble or hair) have no quadrilateral split. Case 1 on class words needs the walk to avoid them, or the l.850 surgeries. ko-closed decides; the surgery split (hs-vanishes hair, leavitt-units bubble) stands.
- leavitt-units found idle since 13:20; the 13:49 ruling had not woken it. Resumed with the (B)-shape order plus (iii') and the co-land notice.

## Rulings 09-13 ~14:05–14:07

- Roster f62aaf7fd records the 14:00–14:05 rulings.
- sec2-sentences, kept cell (ii), PARTIAL: OsinPocketKeptCell 492057fb6 (probe 0913-140023-67387, unwired, queued).
  - exists_kept_of_pocketRegion; exists_kept_of_simple over kh-ejz's PocketWalk.exists_of_exteriorAt + IsSimpleClosedWalk + havoid.
  - No transport needed: OEquivalentDiscDiagram keeps no darts, so X' = S'.diagram from hs-vanishes' OuterSpurThickeningStatement.
  - Blocker 1, the pinched walk: a PocketRegion needs FollowsBoundary. Covered by dgo-analytic's R2 region builder (hull-euler's Euler lemma) or by kh-ejz's U; exists_kept is restated against U if U comes first.
  - Blocker 2, havoid: ruled the absorbed-set version, with "meets implies contained" as a named statement, model-tested first on (a) touching lobes at an empty arc and (b) cell i's face outside the member, via distinct cell arcs.
- jacobson 70f8cd913 OsinPocketLoopCut (probe 0913-135346-38278, unwired, queued): nonempty_osinLoopCut_of_pocketRegion, the R-cell branch of Case 1 one-cell pairs, plus PocketRegion.twoSectionCuts and OsinLoopCut.ofPocketRegion.
  - Binders: GeodesicCollarStatement and PocketCellTransportStatement.
  - Ruled: jacobson owns the producer of OsinLemma94CaseOneSameCellStatement (unowned until now). It composes the cell-free branch (ko-closed's pick: ea9016135 or audit-sec5's metric kill) with the R-cell branch, drafts against ghw-charp2's staged spelling, and lands after (A).
- Wrap pair (13:40 note): no code fix. audit-sec3's single-side face shows fix (b) in Maximal falsifies PartitionInput. The extra side per polygon goes into L, one class per polygon (audit-intro checks). ghw-assembly is free.
- audit-sec3 next: truth audit of GeodesicCollarStatement, PocketCellTransportStatement and PocketPinchLabelledStatement against the pinched two-gon model and Configurations A and B. Verdicts go to the owners.
- root-wire resumed by raw id (wave 14). root-wire and leavitt-units did not wake on by-name sends; a raw-id send woke leavitt-units.
- ko-closed ruling on the one-cell items (roster l.843–850):
  - (1) wins: the metric kill at the printed threshold.
    - WordConnectorPair (UnboundWordConnectors:43-46) has source_long and target_long, and the connectors are geodesic and shorter than ε.
    - Case (a): S = A M B reads a connector, so |val S| < ε (OsinLemma94OneCellValue 36524dbf0, probe 0913-135819-58619, queued).
    - Morse radius κ from exists_word_replacement_morse after isHyperbolicSpace_cayley_of_fourPoint; δ, λ, c are bound before eps0 (PlanarPieces:397), so no statement changes.
    - d(x0,x1) + d(x1,x3) ≤ 2κ + d(x0,x3), plus λ|B| − c ≤ d(x1,x3), give λε − c < 2κ. So any ε₀ > (2κ + c)/λ kills case (a).
    - No DartMinimal, Maximal or least area.
  - The λ⁻¹(ε+c) respelling is CANCELLED: hull-unbound's Dense draft is dropped and sec5-sentences' ρ₀ fold is not needed.
  - Correction to ko-closed 8e9f6b1ce: Shape 1 is not a counterexample at the printed threshold.
  - ko-closed writes (1) in a new module over OsinLemma94OneCellValue.
  - (2): jacobson's nonempty_osinLoopCut_of_pocketRegion stays, and audit-sec5 writes no second LoopCut producer.
  - T threading (OsinLemma97Below) stays with theoremc-retire and lands as its own co-probe after (A).
- hull-unbound next: model test of theoremc-retire's gap finding (can CaseOneWalk produce a gap-containing pair; would gap-free endpoints lose the ClassCovers count). Verdict to ko-closed and theoremc-retire.
