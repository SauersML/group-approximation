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
