# systolic-counts lane report

Lane `systolic-counts` (clone `stw-fix`).  Roster target: make the red `GGT/SystolicDiscCounts` green and
close it.  Also: the filling inputs `ha hb hc hd` of `fillingStatement_of_simplyConnected`
(`GGT/SystolicDiscFilling.lean:126`), and `hcount hsum` of the alternative Kotowski–Ollivier route.

## 09-13 status

### Roster target: closed on main, no edit needed

* `GGT/SystolicDiscCounts` is no longer red.  go-sr1's 4c12845a1 (09-12 10:34) fixed it together with
  `GGT/SystolicDiscFilling`: probe 0912-103604-11425 (base 3221a02ea) was green, md5 Counts 3330bc17,
  Filling f5f0eb23.  Those bytes are the bytes on main now.
* Current-infrastructure evidence: ko-closed's probe 0913-011617-71747 (base e499fdc3e, record
  `lanes/ko-closed.green.0913-011617-71747`) built `Kazhdan.KotowskiOllivierClosed` GREEN.  That module
  imports `Kazhdan.GHBHyperbolicDiscCounts`, which imports Counts, Filling, `SystolicDiscMovesChord` and
  `SystolicDiscMovesAdapter`.  Every `#audit_axioms` line in them passed.
* Closed endpoints, each followed by `#audit_axioms`:
  * `TriangulatedDisc.exists_typedCounts` (HC11) and `TriangulatedDisc.abs_boundarySum_le` (HC12),
    `GGT/SystolicDiscCounts.lean:417-418`;
  * `TriangulatedDisc.oneEdge` (HC2), `fillingStatement_of_simplyConnected` (HC4) and
    `exists_leastDisc_typedLinks_of_simplyConnected`, `GGT/SystolicDiscFilling.lean:162-164`.

### HC3(d), pinch case, for every triangle complex: closed

kh-torsion handed this lane the pinch case of `ZipSpurStatement`.  kh-torsion keeps `CycleDisc.zip_fold`
and the assembly `zipSpurStatement_of_zipPinch` (`GGT/SystolicDiscZip.lean`, on main at 9445c7860).
kh-torsion wires the endpoint and queues both modules.

* Prop (kh-torsion's, `GGT/SystolicDiscZipFold.lean:281`, on main):
  `ZipPinchStatement X`.  It covers the case where the corners before `du` and after `dv` lie at one
  vertex, `SameCycle σ (α p) (α dv)`.
* Producer: `Systolic.zipPinchStatement (X : TriangleComplex V) : ZipPinchStatement X` in the new module
  `GGT/SystolicDiscZipPinch.lean` (this lane), landed at d74b84054.
  * Probe 0913-023335-5925 (base 3e9636d74) is GREEN on the landed bytes (md5 fbbf5f90, record
    `lanes/systolic-counts.green.0913-023335-5925`).
  * `#audit_axioms` passed on `isFaceCycle_of_map_injective`, `exists_map_val_eq`, `CycleDisc.zip_pinch`
    and `zipPinchStatement`.  `zipPinchStatement` depends on axioms `[propext, Classical.choice,
    Quot.sound]`.
  * The modules it imports did not change between 3e9636d74 and origin/main 4a9981630.
* Proof:
  * split the vertex (`FoldMap.joined D.map p dv`), which has Euler characteristic 4
    (`PinchLemma.split_euler`);
  * `du` does not reach `p` (`PinchLemma.not_reach_p`), and every dart is reached from `du` or from `p`
    (`PinchLemma.reach_or_reach`);
  * so the part reached from `p` (`CycleDisc.pinchMap`) is planar
    (`CombMap.restrict_planar_of_euler_four`);
  * its exterior cycle is `t ++ s` (`PinchLemma.split_isFaceCycle_rest`), lifted to the subtype and
    rotated to read `s ++ t`;
  * every other dart is off the old exterior cycle.  There the split map rotates faces as the old map
    does, so its faces are old interior triangles.

### HC6, pinched case: offer withdrawn

hfold is closed: fff-periodic's `Systolic.mirrorFold (X) : MirrorFoldStatement X`
(`GGT/SystolicDiscMirrorFold`, 426813b24, probe 0913-052528-4751).  The vertex-split step offered to
fff-periodic (`FoldStage.exists_split_pinch`) is not needed.  This lane wrote no Lean for it.

### W1 pocket glue: cancelled

The lead cancelled the handout.  go-lemma42 wrote `SurgeryPocketGlueVertices`, `SurgeryPocketGlueCount`
and `SurgeryPocketGluePlanar` itself.  This lane wrote no Lean for W1.

### Done: two defects in the non-MF verifier, landed at 736f7ea44

census found both defects in `scripts/check_non_mf_unconditional.py`.  The script has no owner, so the lead
gave this item to this lane.  Landed with `NM_UNVERIFIED=1`; the script is not in
`lanes/systolic-counts.files`.

* False red on hKO.  `resolve` matched a dotted name only against a bare namespace token or a whole
  namespace stack.  `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` (inside
  `GroupApproximation.KMSGroup`) concludes `Manuscript.NonMF.TheoremC.KotowskiOllivierStatement`, a partial
  path, so the producer was filed under a name outside the corpus.  Fix: `resolve_written_name` tries each
  prefix of the declaration's namespace followed by the name against the corpus full names, as Lean does.
  `_unfold` and `classify` resolve with the namespace.  Nothing matches on a shared tail.
* Blind spot on in-place constructions.  `HullSC.CutLift` is built by `have hcl : CutLift … := { … }` in
  `letterStepBound_of_cutLiftOutcome`, and rows 8aead549f1fe and 4895f03fdf5f reported no producer.  Fix:
  `in_place_heads` reads `have`/`haveI`/`let`/`letI [name] : T := ⟨…⟩ | { … }` and `(⟨…⟩ : T)`,
  `({ … } : T)`; each produces `T` under the declaration's requirements and taint.  Refutations and
  sort-valued defs produce nothing this way.
* Calibration on MSI, through a copy of census's `census_run.sh`, on an export of 9b413742b:
  * `PRODUCER_FIXTURE`, now part of `--self-test`: the old script got 7 of its 11 consumers wrong, the
    candidate gets 11 of 11 right.  A Prop with no producer still reports red, a producer resting on
    `sorry` still reports conditional-debt, and the partial-path and in-place shapes come out clean.
  * `--self-test`, the importers' self-tests and `check_ledger_unconditional` pass.  The gate reports 47
    cited declarations unconditional before and after.
* Register effect.  `sentence_census --verify-unconditional` exits 1 until census re-registers
  `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`.  This is the ratchet working, not a candidate bug.
  * 3 stale lines: `HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`,
    `HullSC.CutLift.toCutMove` and `HullSC.cutLiftOutcome` now report header binders only.
  * 169 new findings (145 open-predicate, 19 carrier-data, 2 inlined-statement, 2 buried-conditional,
    1 conditional-data).  The old resolver dropped the partial path
    `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, so the `TheoremC.LiteratureInputs`
    producers over it, `FournierFacioParagraph`, `HullOneStepStatement`, `HullTowerStatementGeneral` and the
    Printed* carriers counted as discharged.
* Trace on MSI, both discharge fixed points compared declaration by declaration:
  * no declaration loses a conclusion or a requirement (0 violations);
  * 35 names gained (producers: 22 in-place, 15 completed conclusions, 24 cascades); spot-checked
    `CutLift`, `KotowskiOllivierStatement`, `Heis`, `IsSpelling`, `LinkCertificateChecks`, all genuine;
  * 51 names lost, each blocked by a Prop undischarged under both scripts:
    `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (143 blocked producers),
    `RelativeGreendlingerQuasiGeodesicStatement` (17), `EstimatingUnboundOutputStatement` (11),
    `EstimatingSelectionConstructionStatement` (11), `RelativeGreendlingerStatement` (1).
* Sent to census and main: the SHA, the 3 stale lines and the grouped findings.  CI "Sentence-level census"
  (`build-non-mf-pdf.yml`) stays red until census re-registers.

### Current item: flip list for the declarations blocked off the ruled route

The ruled route proves only `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (LA).  The lead asked for a
flip list for the declarations that need one of the four Props off that route.  Read-only work:
* three runs on MSI with the landed verifier (md5 69b5e9b4): `sc_flip.py` on 92c643520, `sc_twins.py` on
  004b690d0, and `sc_fcheck.py` on 0183c4b57, which checks each flip pair;
* no Lean file named below, and not the verifier, changed between 004b690d0 and 1b6c528fa.

The list went to nm-endpoints, which owns the wall-only wrappers, with copies to census and main.

* **Status on main.**  No blocker is discharged with LA assumed.
  * `EstimatingUnboundOutputStatement` (`GGT/VanKampen/Estimating/Assembly.lean:826`) is refuted.
    * The refutation is `Estimating.UnboundScaledCounterexample.not_estimatingUnboundOutputStatement :
      ¬ EstimatingUnboundOutputStatement.{0, 0, 0}` (`UnboundScaledCounterexample.lean:192`): no binders,
      root-imported.
    * Its one producer, `estimatingUnboundOutputStatement_of_scaledDecomposition`
      (`UnboundScaledDecomposition.lean:113`), needs `Lemma62ScaledDecompositionStatement`.
    * The def's docstring (`Assembly.lean:818`) still says "Still open, and not addressed here", which is stale.
    * Nothing on main refutes the `{u, w, 0}` or `{u, w, v}` spellings.
  * `EstimatingSelectionConstructionStatement` is open, with no refutation.  Its producers need
    `Lemma65aDichotomyStatement` (`SelectionDichotomy.lean:151`) or `Lemma65aOrderedDichotomyStatement`
    (`SelectionOrderedDichotomy.lean:90`).
  * `RelativeGreendlingerQuasiGeodesicStatement` (RGQG) is open, with no refutation.  Each of its four producers
    needs one of:
    * `EstimatingDataConstructionStatement` (`Assembly.lean:1031`);
    * Selection with Unbound (`:1039`);
    * `EstimatingJointConstructionStatement` (`EndpointClosedAssembly.lean:199`);
    * `EmbeddedEstimatingSystemConstructionStatement` (`RelativeGreendlinger.lean:392`).
  * `HullSC.RelativeGreendlingerStatement` (RGS) is open, with no refutation.
    * The `GGT.VanKampen` name is an alias (`RelativeGreendlinger.lean:459`).
    * Producers: `HullSCRelativeGreendlingerFromComponents.lean:144` and `:421`.
    * The only second-level refutation, `not_relativeExteriorArcConversionAtWordStatement`
      (`ExteriorArcCounterexample.lean:359`), refutes the AtWord variant.  Neither producer of RGS names it.
* **Bridges.**
  * The one bridge on main, `relativeGreendlingerQuasiGeodesicLeastArea_of_reduced`
    (`Estimating/OsinAppendixSectionBridge.lean:69`), runs from RGQG to LA.  It cannot feed a consumer from
    LA, and main has no bridge from LA to an off-route Prop.
  * The least-area forms below take LA, plus the embedded bridge where they need it.  That bridge is proved at
    `{0, 0, 0}`, with no premises, by `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
    (`GGT/HullSCLemma51EmbeddedBridgeHolds.lean:20`).
    * The verifier flags that theorem as buried-conditional (row 4895f03fdf5f).
    * The statement it proves, `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedAt`
      (`HullSCLemma51EmbeddedBridge.lean:92`), is an implication.  Its antecedent asks for a
      `RelativeDiagramCertificate` for every least-area diagram with a quasi-geodesic spelling.
    * So the theorem is closed, but it gives embeddedness only to a caller who supplies those certificates.
  * It replaces `RelativeIsoperimetricBridgeQuasiGeodesicStatement` (`HullSCLemma44QuasiGeodesicBridge.lean:177`),
    which has no producer.  Every `_of_leaves` form needs it, and so does every `_of_quasiGeodesicLeaves` form
    except `hullLemma49KernelPowerStatement_of_quasiGeodesicLeaves` (:85).
* **Census.**
  * Of the 366 official findings, 307 clear under LA alone, and none is blocked only by an off-route Prop.
    * Assuming all four off-route Props as well clears none of the other 59.
    * By kind, the 59 are 28 carrier-data, 12 buried-conditional, 12 open-predicate, 4 conditional-data and
      3 inlined-statement.
    * Most are on the `GloballyDistinguishedSectionFamily` predicates, the `OsinLemma94*Input` carriers and
      `GFaceMerge`.
  * No counted row of the merged `NON_MF_SENTENCE_MAP.tsv` names any of the 86 in `decls`.  Rows 721da4c14d11,
    2d1cd22e5f49 and 2f997e5af4e6 mention the `TorsionFreeSectionSentences` `_of_leaves` forms only in the note.
  * Two lane files still name historical forms in `decls`:
    * `metadata/nm-census-rows/hull-respell.tsv`: LINE:1636 names `hullOneStepStatement_of_quasiGeodesicLeaves`,
      `hullBallFormNG_of_quasiGeodesicLeaves` and `hullInputsCorrected_of_quasiGeodesicLeaves`.  LINE:1644 names
      the first two.  Neither row is in the merged map.  Flip targets: BLC:140, `hullBallFormNG_of_oneStep` over
      BLC:140, and `TorsionFree.hullInputs_of_leastAreaLeaves`.
    * `metadata/nm-census-rows/sec5-sentences.tsv`: LINE:1662, 1665 and 1698 name each `_of_leaves` form
      beside its least-area twin.
  * 11 names are discharged only when the off-route Props are assumed.  None has a census row.
* **Verdicts for the 86.**  Key: `T` = `GGT/HullSCLeastAreaGreendlingerTwins.lean`, `BLC` =
  `GGT/HullSCLemma44BoundedLeastAreaCanonical.lean`, `LAA` = `Manuscript/NonMF/TorsionFreeLeastAreaAssembly.lean`.
  `sc_fcheck.py` on 0183c4b57 checked all 49 pairs, since :173 has two targets.  Each target is root-reachable
  and not `sorry`-tainted, and each requirement it names is discharged under LA, where the embedded bridge counts
  as discharged, with the caveat above.  None adds a requirement the consumer lacks.  The two nearest forms named
  under Superseded, BLC:44 and BLC:123, pass the same check.  `HullLemma44CanonicalQuotientStatement` has 22
  producers, but it is not discharged under LA.
  * **Flip, 48: a least-area form exists.**
    * `HullSCLemma44CertificateInjectivity` :143 → T:311 `exists_relativeBallInjectivityParameters_of_geodesicLengthLeastAreaGreendlinger`.
    * `HullSCLemma49Assemble` :65, :160, :172, :193 → T:883 `hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_leastAreaGreendlinger`
      (:193 also drops `PrefixKernelConeTransferStatement`).
    * `HullSCLemma49PowerDiagramFromComponents`:
      * :69, :87, :126 → T:883;
      * :104, :139 → T:896 `hullLemma49KernelPowerStatement_of_leastAreaGreendlinger`;
      * :152 → T:311.
    * `HullSCLemma49SourceAssembly` :90 → T:772 `hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_sourceBranches`.
    * Long period → T:447 `exists_parameters_false_of_longPeriod_leastAreaPowerDiagram_source`:
      `HullSCLemma49FixedDelta` :24, `HullSCLemma49LongPeriod` :94, :151, `HullSCLemma49SourceBranches` :53.
    * Short loxodromic → T:547 `exists_parameters_false_of_shortLoxodromic_leastAreaPowerDiagram_source`:
      `HullSCLemma49FixedDelta` :81, `HullSCLemma49ShortLoxodromic` :145, :293, `HullSCLemma49SourceBranches` :168.
    * `HullSCLemma49InjectivityBridge` :46 → T:354 `hullLemma49InjectivityCallback_of_geodesicLengthLeastAreaGreendlinger`.
    * `VanKampen/RelativeDiscRealizationPowerCertificate` :100 → T:47 `lemma49Certificate_of_relativeGreendlingerLeastArea`.
    * `HullSCRelativeGreendlingerQuasiGeodesicSpelling` :117, :188, :219 and `TorsionFreeLeafAssembly` :93 →
      T:126 `relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger`.
    * `HullSCRelativeGreendlingerSpelling` :335, :407 and `HullSCRelativeGreendlingerGeodesicConsumers` :154 →
      T:211 `relativeGreendlingerGeodesicLengthLeastAreaStatement_of_leastAreaGreendlinger`.  `GeodesicConsumers` :127 → T:311.
    * `HullSCOneStepQuasiGeodesicLeaves`:
      * :85 → T:896;
      * :98 → BLC:140 `hullOneStepStatement_of_leastAreaLeaves`;
      * :115 → `hullBallFormNG_of_oneStep` (`GGT/HullSC.lean:625`) over BLC:140; no single named form exists;
      * :126 (a def) → `TorsionFree.hullInputs_of_leastAreaLeaves` (`Manuscript/NonMF/TheoremCAssembly.lean:259`).
    * `TorsionFreeLeafAssembly`:
      * :113 → T:896;
      * :126 → BLC:140;
      * :142, :152, :164, :173, :262 → LAA:38, :47, :57, :66, :78.  :173 also has
        `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` (`TheoremCAssembly.lean:333`).
    * `TorsionFreeSectionAssemblyClosedGO` :61 → :74 `manuscriptRegularNonMFAlgebra_of_leastAreaLeaves_closedCitations`.
    * `TorsionFreeSectionSentences`:
      * :71 → `TorsionFreeHullPrintedLeastArea.lean:32` `manuscriptSentence_hullTheorem_of_leastAreaLeaves`,
        which states the theorem at every group;
      * :93, :126 → the same file :58, :72, the `TorsionFreeHullParagraphGeneral` `...General_of_leastAreaLeaves`
        forms;
      * :165, :188, :210 → `TorsionFreeSectionSentencesLeastArea.lean:37`, :57, :75.
  * **Superseded, 37: docstring mark only, no deletion.**  No least-area form has the same conclusion.
    * `HullSCLemma44BoundedFilling` :58.
    * `HullSCLemma44Canonical` :131, :203, :218, :293, :301, :309, :317, :341, :349, :358, :371, :443, :454, :528.
      * Each needs RGS and a transfer Prop, and `HullLemma44CanonicalQuotientStatement` is not discharged under LA.
      * The nearest least-area form, BLC:44 `boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea`,
        has the bounded conclusion.
      * :341 and :349 already carry VACUOUS: `RelativeLinearAreaTransferStatement` is refuted.
    * `HullSCLemma44CertificateInjectivity` :191; `HullSCLemma44FamilyAssembly` :545, :652, :667;
      `HullSCLemma44KernelAssembly` :274, :326, :380.
    * `HullSCLemma44RelativeGreendlingerAdapter` :63, :110, :150, :189, :238.  Every user of these witnesses is
      off route itself.
    * `HullSCLemma49InjectivityBridge` :84.
    * `HullSCLemma49RebasedCertificate` :80.  Its four users flip to T:447 and T:547, which go through T:47.
    * `HullSCOneStepQuasiGeodesicLeaves` :71, nearest BLC:44.
    * `TorsionFreeLeafAssembly` :103, nearest BLC:123 `torsionFreeHullCanonicalQuotientStatement_of_leastAreaLeaves`
      (torsion-free conclusion).
    * `HullSCRelativeGreendlingerFromComponents` :104, :359, :421.
    * `HullSCRelativeGreendlingerPowerBoundary` :87: no least-area `SpellingAt` statement exists.
    * `VanKampen/Estimating/Assembly` :849, :1039.  These produce off-route Props.  The ruled route is
      `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts` (`OsinAppendixGreendlingerPocketParts.lean:131`).
  * **Keep, 1:** the bridge `OsinAppendixSectionBridge` :69.
  * **Vacuous, 11.**  These state the Unbound premise at `{0, 0, 0}`, where it is refuted:
    `HullSCLemma49Assemble` :172, :193; `HullSCLemma49PowerDiagramFromComponents` :87, :104, :126, :139;
    `HullSCOneStepQuasiGeodesicLeaves` :71, :85, :98, :115, :126.

## Brief items

| input | producer on main | state |
|---|---|---|
| `ha : AttachTriangleStatement X` | `Systolic.attachTriangleStatement`, `GGT/SystolicDiscMovesChord.lean:298` | closed (kh-torsion) |
| `hb : InsertChordStatement X` | `Systolic.insertChordStatement`, `GGT/SystolicDiscMovesChord.lean:254` | closed (kh-torsion) |
| `hc : AttachPendantStatement X` | `Systolic.attachPendantStatement`, `GGT/SystolicDiscMovesAdapter.lean:136` | closed (kh-torsion) |
| `hd : ZipSpurStatement X` | `Systolic.zipSpurStatement` and `CCKW.zipSpur_cosetComplex`, `GGT/SystolicDiscZip.lean:122,131` | closed (kh-torsion, 8389a0e6c, probe 0913-030432-13308), from `Systolic.zipPinchStatement` (this lane) |
| `hcount` | `CCKW.typedCountStatement_cosetComplex`, `Kazhdan/GHBHyperbolicDiscCounts.lean` | closed (kh-hyperbolic) |
| `hsum` | `GHBHyperbolicStokes.boundarySumStatement`, `Kazhdan/GHBHyperbolicDiscCounts.lean:56` | closed (kh-hyperbolic) |
| hfold `MirrorFoldStatement X` | `Systolic.mirrorFold`, `GGT/SystolicDiscMirrorFold` | closed (fff-periodic, 426813b24) |

## Residual Props

* None from this lane.

## Wiring

* `GGT.SystolicDiscCounts`, `GGT.SystolicDiscFilling`, `GGT.SystolicDiscMovesChord` and
  `Kazhdan.GHBHyperbolicDiscCounts` are not yet reachable from the root.  This lane queued
  `GroupApproximation.GGT.SystolicDiscCounts systolic-counts 4c12845a1`.
* kh-torsion queued `GGT.SystolicDiscZipPinch systolic-counts d74b84054` and
  `GGT.SystolicDiscZip kh-torsion 8389a0e6c`.  The root imports `GGT.SystolicDiscZip` since c72bdfd5d,
  and `SystolicDiscZip` imports `SystolicDiscZipPinch`, so this lane's module is in the root closure.
* Stale notes:
  * wire-queue line 318, "GHBHyperbolicDiscCounts waits on red Filling/Counts";
  * the `EdgeInsertion.embed_injective` hold on `EdgeInsertionFaceCycles` and `SystolicDiscMovesChord`,
    because 6a5f25704 renamed the lemma to `embed_injective_faceCycles`;
  * census2 line 52, "red `GGT/SystolicDiscCounts`".

## Next

* nm-endpoints and the flip owners apply the flips and superseded marks above, docstrings only.  This lane lands
  no Lean edit for this item.
* The "Still open" docstring on `EstimatingUnboundOutputStatement` (`Estimating/Assembly.lean:818`) should name
  the `{0, 0, 0}` refutation.  The owner of that file makes the edit.
* census decides on the historical forms in `hull-respell.tsv` LINE:1636/1644 and `sec5-sentences.tsv`
  LINE:1662/1665/1698.
* If census's re-registered baseline against 736f7ea44 has a finding that points at the verifier, not at the
  corpus, this lane fixes the script and re-runs the calibration on MSI.
* Otherwise idle until the lead assigns a new item.
