# Lane ms-compress-1: tex 358–467 (sec:compression-radical opening, prop:mf-residual-calculus, lem:stable-finite)

Snapshot: origin/main 3b61ba8b2 (2026-09-13 ~16:50 CDT). Rows come from `metadata/NON_MF_SENTENCE_CENSUS.tsv`, where these
sentences sit at lines 352–451 because that file predates the chain-core section. All 26 rows in the range are assigned.
Every carrier module is reachable from `GroupApproximation.lean` (import closure computed over origin/main).

## Ledger

| key | tex (68481e4d7) | status | carriers | verdict |
|---|---|---|---|---|
| 6a52924d8260 | 364 | structural | — | OK (setup) |
| a8e4ac99b640 | 364–366 | formalized | `OneSidedMFRadical.allMFTargetsKill_iff_allCoronasKill` | OK. Targets are countable, as in the printed definition (tex 87: MF is defined for countable groups) |
| db7009c5a941 | 366–367 | structural | — | OK (setup) |
| 3bd1b6ab184a | 367–368 | formalized | `isCDEOperatorMF_of_faithful_corona_map` | OK (injective, possibly nonunital, star homomorphism into the corona; G countable) |
| bd2989c81dc3 | 368–370 | formalized | `manuscriptSentence_appliesToMaximalCanonicalMap`, `..._appliesToReducedCanonicalMap` | OK |
| 46d40014ee9e | 376 | formalized | `manuscriptSentence_coronaImageIsCountableMF` | OK |
| 6c597e046078 | 376–378 | formalized | `manuscriptSentence_composeMFHomWithCoronaEmbeddingSameKernel` | OK |
| bee886268f33 | 379–381 | formalized | `manuscriptSentence_nonunitalCoronaHomInjectiveOnG` | OK |
| 07de7e8a943a | 384–390 | formalized | `manuscriptSentence_blockSumFamily`, `..._mfRadicalQuotientResidualTrivial`, `..._mfRadicalQuotientIsMFAndLargest` | OK (the block-sum route is exposed; Rad_MF is identified with the corona residual) |
| 8e54f4138ac7 | 390–391 | formalized | `manuscriptSentence_blockSumFamily` | OK |
| fd2cafafd8fa | 395–400 | formalized | `CompressionCriterionSentences.manuscriptSentence_exactRepresentationCommutantDimensionCount` | OK (any field and finite-dimensional V, which covers U(d)) |
| b1b62a9e3c06 | 400–401 | structural | `..._asymptoticRepresentationHasNoExactCommutant` | OK (motivational sentence) |
| 240357aed76a | 402–403 | formalized | `..._kazhdanProjectionAndStableFinitenessReplaceTheCount` | OK |
| 399d33df9009 | 405–409 | definition | `hsNorm` | OK (normalized trace) |
| 629f562df6bc | 410–415 | definition | `OpAlmostRepresentation` | **GAP G1.** The structure has no field `V_n(1) = 1`. The comment at `CompressionSentencesA.lean:179` ("with V_n(1)=1 built into the unitaryGroup coercion") is false |
| b093f3c88101 | 416–424 | formalized | `manuscriptSentence_hsNullNormalSubgroupPrintedRoute`, `printedHSNullSubgroup`, `printedHSNullSubgroup_normal`, `mem_printedHSNullSubgroup_iff_mem_hsKernel` | OK |
| db30dea6e7f0, c9b981a3a338 | 425–434 | definition | `TransportPrintedCommutant.printedCTwo` | OK |
| 630db09c6f46 | 434–436 | definition | `adSequence`, `manuscriptSentence_adSequenceBijective` | **GAP G2.** The bijection is proved on all sequences. The printed restriction to Hilbert–Schmidt bounded sequences is argued only in a docstring |
| 186ab929187a | 437–438 | definition | `IsCStarFinite`, `IsCStarStablyFinite` | OK |
| 6b1c6779ed70, da52971fd39a, a594de997cbe | 440–447 | formalized | `NormMatrixCStarCorona`, `manuscriptNormMatrixCoronaStableFinite`, `manuscriptStableFinite`, `manuscriptSentences114_115_normMatrixCorona_stableFinite` | OK (both clauses; the Lean hypothesis is an isometry, more general than a unitary) |
| fc6ea69c0036 | 451 | definition | `stableFiniteCorona` | OK |
| 6b308543eb28 | 451–455 | formalized | `sentence_8461ba613634`, `sentence_0ac3ff393cfe`, `sentence_fc7ae023c534`, `sentence_974e2b57e3ef`, `sentence_ee3d6cbf975d` | OK (polar-correction route) |
| daecb970c06a | 455–456 | formalized | `sentence_993df6a79c44`, `sentence_36cd63cf2803_stablyFinite`, `MatrixAmplificationCoronaIsomorphism`, `sentence_b21cf7f0f627` | **GAP G3 (route).** M_k(A) is shown finite by a Neumann-series route. No declaration transfers finiteness through the printed identification of M_k(A) with the corona of sizes km_n. The row also names the Prop `MatrixAmplificationCoronaIsomorphism` instead of the theorem `sentence_36cd63cf2803_isomorphism` |
| 5e9b44d1c0bb | 457–460 | formalized | `sentence_70c4de929477`, `sentence_9b9e5b396d6f` | OK (G4 checked). `sentence_70c4de929477` calls `cstar_eq_of_murrayVonNeumannEquiv_of_absorbs`, whose ring-level proof `eq_of_murrayVonNeumannEquiv_of_absorbs` runs the printed route: r = rq and r = qr (that is, w = qwq), σ = r + (1 − q) is an isometry, finiteness makes σ unitary, and σσ* = p + (1 − q) = 1. The hypothesis is finiteness, as printed. Only the docstring wording of `sentence_9b9e5b396d6f` is stale ("stably finite") |
| 86ee71463acf | 463–466 | definition | `KazhdanData.projection`, `manuscriptSentence_kazhdanProjection`, `kazhdanProjection_central` | OK. A closed theorem with no literature input (the AkemannWalter fact is proved) |

## Claims

- CLAIM G1 printed operator norm asymptotic representation (`V_n(1) = 1`) and its normalization GroupApproximation/Manuscript/NonMFSentences/CompressionRadicalPrintedObjects.lean
- CLAIM G2 `Ad(V(g))` is a bijection of the Hilbert–Schmidt bounded sequences GroupApproximation/Manuscript/NonMFSentences/CompressionRadicalPrintedObjects.lean
- CLAIM G3 M_k(A) is finite through the amplification isomorphism GroupApproximation/Manuscript/NonMFSentences/CompressionRadicalPrintedObjects.lean
- CLAIM G5 named closed-endpoint Props for four range endpoints GroupApproximation/Manuscript/NonMFSentences/CompressionRadicalClosedEndpoints.lean

## Landed

- **G1, G2, G3 CLOSED: aae8a52a1** (`Manuscript/NonMFSentences/CompressionRadicalPrintedObjects`; probe 0913-171434-13022 GREEN, BUILT, md5 of the landed bytes matches the record). Queued for wiring.
  - `PrintedOpAsymptoticRepresentation`: extends `OpAlmostRepresentation` with `map_one : ∀ n, map n 1 = 1`. `normalizeOne` resets any `OpAlmostRepresentation` at `1`. Closed endpoint `printedAsymptoticRepresentationNormalization`: the reset satisfies `V_n(1) = 1` and differs from the original by an operator norm null sequence.
  - `printedAdBijectionOfHSBoundedSequences : PrintedAdBijectionOfHSBoundedSequences` is `Set.BijOn (adSequence B g)` on `{x | IsHSBounded B x}`, via `hsNorm_adSequence` (unitary conjugation preserves the normalized Hilbert–Schmidt norm).
  - `printedMatrixCoronaFinite_viaAmplification` transfers isometry ⇒ unitary through `matrixCoronaAmplificationEquiv` and `sentence_993df6a79c44`. `printedCoronaStablyFiniteViaAmplification` gives `IsCStarFinite A ∧ IsCStarStablyFinite A` along that route.
- Census rows for 629f562df6bc, 630db09c6f46 and daecb970c06a: `metadata/nm-census-rows/ms-compress-1.tsv`.

## Audit coverage (origin/main, checked 17:25)

- Every range endpoint passes an axiom audit. Plain `#audit_axioms` also enforces the classical allowlist: a probe of this lane's first draft failed with "depends on axioms outside the classical allowlist" on a plain audit.
- **G5:** four endpoints have only a plain audit (Audit/Sec2.lean:97, 101, 127, 135) and no named-Prop spelling that `#audit_closed_axioms` accepts (COMMON_RULES rule 10). Their types start with binders, so the closed audit rejects them as stated:
  - `isCDEOperatorMF_of_faithful_corona_map`
  - `OneSidedMFRadical.allMFTargetsKill_iff_allCoronasKill`
  - `CompressionCriterionSentences.manuscriptSentence_kazhdanProjectionAndStableFinitenessReplaceTheCount`
  - `CompressionCriterionSentences.manuscriptSentence_exactRepresentationCommutantDimensionCount`
- The fix is additive: a new module with `def Printed… : Prop` and theorems proved by the existing declarations, each carrying `#audit_closed_axioms`. No existing file is edited.
- **G5 CLOSED: 43c01c44f** (`Manuscript/NonMFSentences/CompressionRadicalClosedEndpoints`; probe 0913-173237-77904 GREEN, BUILT). Closed endpoints:
  - `printedAllMFTargetsKillIffAllCoronasKill : PrintedAllMFTargetsKillIffAllCoronasKill`
  - `printedFaithfulCoronaMapGivesMF : PrintedFaithfulCoronaMapGivesMF`
  - `printedExactRepresentationCommutantDimensionCount : PrintedExactRepresentationCommutantDimensionCount`
  - `printedKazhdanProjectionAndStableFinitenessReplaceTheCount : PrintedKazhdanProjectionAndStableFinitenessReplaceTheCount`
  - Queued for wiring. Census rows a8e4ac99b640, 3bd1b6ab184a, fd2cafafd8fa and 240357aed76a are in `metadata/nm-census-rows/ms-compress-1.tsv`.

## Range status (2026-09-13 ~17:40)

- Every sentence of tex 358–467 is carried by a closed, root-reachable declaration at the printed generality along the printed route, or is honestly classified: three `structural` setup or motivation rows and `definition` rows with carriers.
- The range has no literature input. The one `\cite` in the range, AkemannWalter at tex 466, is carried by the closed theorem `manuscriptSentence_kazhdanProjection`, which proves existence, centrality and the fixed-vector image.
- Wiring pending: `CompressionRadicalPrintedObjects` (aae8a52a1) and `CompressionRadicalClosedEndpoints` (43c01c44f). Until root-wire takes them, the new carriers of rows 629f562df6bc, 630db09c6f46, daecb970c06a, a8e4ac99b640, 3bd1b6ab184a, fd2cafafd8fa and 240357aed76a are not root-reachable. The existing carriers of those rows already are.
- Stale docstrings, no mathematical defect (owners: CompressionSentencesA and StableFinitenessSentences have no active lane):
  - `CompressionSentencesA.lean:179` says `V_n(1) = 1` is "built into the unitaryGroup coercion". It is not; see `normalizeOne`.
  - `StableFinitenessSentences.sentence_9b9e5b396d6f` quotes "a stably finite algebra"; the printed proof now says "a finite algebra".

## Census successor: sec:chain-core rows for down lanes (main's item, 09-13 ~18:45)

Keys and owners come from the ms-core-2 ledger (4130c32d3, tex 1371–1458) and the ms-core-4 ledger (adbf70b62, tex 1516–1540). Carriers were read at origin 65c39f1d6 against the printed text (tex byte-identical to 68481e4d7). The down lanes are chain-words, chain-subshift, chain-itinerary, chain-reflection, hull-euler (S2) and chain-core (S1).

### Rows appended (`metadata/nm-census-rows/ms-compress-1.tsv`)

| key | tex | status | carriers | module state |
|---|---|---|---|---|
| `53fd5ea7d3d0` | 1380 | structural | setup; subshift hypotheses as ordinary hypotheses | SubshiftWordGraph (root) |
| `9bc3873fb872` | 1380–1382 | definition | `WordGraph.word`, `language`, `wordEdge`, `wordGraph` | root |
| `078684fc2a60` | 1383–1384 | definition | `WordGraph.IsCyclicEdge`, `CycleCondition` | root |
| `4bb19e581840` | 1432–1433 | formalized | `isCyclicEdge_comp`, `cycleCondition_image_comp`, `cycleCondition_oneBlock_image` | OneBlockCycleCondition dd08aab94, unwired |
| `b180421b55ab` | 1439–1441 | partial | `cycleCondition_iInter_of_antitone`, `cycleCondition_iInter_oneBlock_image`, `cycleCondition_itinerary_image_generalCore` | ItineraryCoreCycleCondition dd08aab94, unwired; residual `hcore : ∀ l, CycleCondition (itineraryCore T (S l))` = tex 1411 `647f44a95b8a` (ms-traces-3) |
| `fe2bd83087c0` | 1429–1432 | formalized (re-grade of chain-itinerary partial) | `itinerary`, `itinerarySubshift`, `oneBlock` (d616d6bcb), `itineraryCore` (dd08aab94) | unwired |
| `ed348643e2ad` | 1433–1438 | formalized (re-grade) | `oneBlock_image_itineraryCore_subset`, `generalCore`, `itinerary_image_generalCore` | unwired |
| `807793f12a5e` | 1439 | formalized (re-grade) | `itinerary_image_inverseLimitCore`, `itinerary_image_generalCore` | unwired |

Route note on `ed348643e2ad`: ρ_lm(Y_l) ⊆ Y_m is proved from the cyclic-edge characterization of the core (tex 1412) plus "cycles map to closed walks". It does not need the cycle condition of Y_l (tex 1411).

### Skipped: owned by live lanes (they keep their own rows)

- **ms-traces-3** took the symbolic LEF proof and cycle conditions that chain-words and chain-subshift left unlanded; the boundary is recorded in ms-core-2.md.
  - Keys: `dfc6d4510272`, `8bf7f40918d5`, `56b6a80cc911`, `2ed7f807a3a6`, `57cd1b63930c`, `0941296cf395`, `4aede6d48b4d`, `b94a006ee638`, `533771f4f22d`, `cbf45b0e1c51`, `1d52a79f1fef`, `647f44a95b8a`.
  - `2ed7f807a3a6` already has a landed chain-words carrier, `exists_periodic_of_isCyclicEdge` (6078315b6, unwired). `0941296cf395` consumes `Pestov91.periodicModel` and `shiftMatrix` on main. Both are steps inside the adopted SubshiftCycleLEF proof.
  - chain-subshift's partial rows `f7c8d8aab016` and `ded9e9646e4b` (residual: nonemptiness) wait on the same lane.
- **ms-core-2** (general-X LEF, `Y_* = Y`, factor pullback): `c825bc73828a`, `2df08eeac3cb`, `e6626f95fede`, `2583cbd0c0f2`, `3b218f92cd81`, `fb195144e5c2`, `8921296d639a`, `c99bf0bdb029`, `d8e1a694d87c`. Its modules ChainCoreGeneral{Factor,LEF,Recurrent} and CoreModelsLEF are not on origin yet.
- **ct-return-tower** owns the printed assembly of thm:core-ring-reflection (`Manuscript/NonMFSentences/CoreRingReflection.lean` in its `.files`, attic e8daa265e). That covers all 12 chain-reflection keys: `42c043ef7ab5`, `8981cd70915a`, `43afa4ee3f10`, `cfbacaa0fffa`, `9dae685e37b9`, `400dde0dbd9d`, `5a62e295ac1a`, `d74779471003`, `715cbd0f3410`, `30a44485e5e8`, `f2baa4a46f78`, `b23e0f5197b5`.
  - Stale residuals on chain-reflection's rows, already discharged on origin:
    - `LEFStablyFiniteInterface` by `lefStablyFiniteInterface` (5932d213f);
    - `I = 0 ⇔ X = Y` by `transientIdeal_eq_bot_iff` and `restrict_injective_iff` (TransientIdealExact 4af014f74);
    - defect generation by `transientIdeal_chainRecurrentSet_eq_span` (784fe34ad).
  - `R_Y` LEF is still open (`CoreModelsLEFStatement`, ms-core-2).
  - All of these modules are unwired.

### Skipped: no carrier on origin

- `042966c81c7e` (tex 1456), "Pull back the symbolic defects to cover X∖Y by their translates". chain-itinerary planned `exists_defect_translate_of_not_mem_chainRecurrentSet`, which is not on origin, and no live lane records a claim on it. Unowned: needs an owner from main.

### Already rowed by down lanes, verified unchanged

- hull-euler: `0ae6fc9e199c`, `73bd8ac910aa`, `3ef2a7cdb9bd` (ChainRecurrenceCovering 5b63c946c, unwired).
- chain-subshift: the definition and formalized rows.
- chain-itinerary: `3d8a2204752a`.
- chain-core: `549aa93e832f`.

## For the census lane

- When the new carriers land, 629f562df6bc, 630db09c6f46 and daecb970c06a gain them. 5e9b44d1c0bb gains one if G4 finds a route gap.
- daecb970c06a should name the theorem `sentence_36cd63cf2803_isomorphism`, not the Prop.

## CLAIM (main's item 09-13 ~19:10): tex 1456 `042966c81c7e`

- CLAIM pulled-back symbolic defects cover X∖Y, along the printed route GroupApproximation/Dynamics/ChainCoreDefectPullback.lean
  - `pulledBackDefect T S r b = π_S⁻¹(reachableCylinderUnion X_S r b)`: clopen, T(Q) ⊆ Q; a noncyclic window at position i of π_S(x) gives T^{i+1}x ∈ Q∖T(Q).
  - Covering: x ∉ Y_* gives a noncyclic window (`mem_coreSubshift_iff`), and Y_* ⊆ Y (`generalCore_subset_chainRecurrentSet`, ms-core-2 0bdeb7074) covers X∖Y.
  - Printed-route carrier also for statement key `0ae6fc9e199c` (hull-euler's carrier is the direct atom-graph covering).
  - Ownership check at origin 2f116d20d: no chain-itinerary draft (its .files hold landed bytes only), no shared-tree draft, no lane holds the path.
- **CLOSED: 51734ad4c** (`Dynamics/ChainCoreDefectPullback`; probe 0913-193823-99328 GREEN with a BUILT line; the log has no error, warning or sorryAx line). Queued for wiring. It imports ms-core-2's `ChainCoreGeneralRecurrent`, which is also unwired.
  - `pulledBackDefect T S r b := itinerary T S ⁻¹' reachableCylinderUnion (itinerarySubshift T S) r b`.
  - `isClopen_pulledBackDefect`: the preimage of a word cylinder under the continuous itinerary map.
  - `mapsTo_pulledBackDefect`: `T(Q) ⊆ Q`, via `itinerary_apply_self` and `mapsTo_shift_reachableCylinderUnion`.
  - `zpow_succ_mem_pulledBackDefect_diff`: a noncyclic window of `π_S(x)` at position `i` gives `T^{i+1} x ∈ Q ∖ T(Q)`, through chain-subshift's `shift_mem_diff_of_not_isCyclicEdge`.
  - `exists_mem_zpow_image_pulledBackDefect_diff`: `x ∉ Y_*` gives a noncyclic window (`mem_coreSubshift_iff`) and lies in `T^{-(i+1)}(Q ∖ T(Q))`.
  - `compl_chainRecurrentSet_subset_pulledBackDefects`: X∖CR(T) is covered for refining partitions, via `generalCore_subset_chainRecurrentSet`.
  - Closed endpoints:
    - `printedPulledBackDefectsCover : PrintedPulledBackDefectsCover` (tex 1456, plus clopenness, invariance and wandering of the pulled-back sets);
    - `printedChainCoreCoveringPrintedRoute : PrintedChainCoreCoveringPrintedRoute` (tex 1373–1374, in the format of hull-euler's `PrintedChainCoreCovering`, for compact totally disconnected metric X).
  - Census rows: `042966c81c7e` formalized. `0ae6fc9e199c` is formalized with the printed-route carrier added; hull-euler's direct covering stays as a second carrier.
  - First probe 0913-192858-57085 was red: a membership goal was written with `∈ _`, and the stuck instance cascaded to sorryAx. Fixed by naming the set.

## CLAIM (main's item 09-13 ~19:55): `OsinLemma94LongTransitionInput` (W1 leaf; owner sec5-sentences, down)

- CLAIM proof of OsinLemma94LongTransitionInput GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94LongTransitions.lean
  - Route (sec5-sentences.md l.330–340, roster l.1273–1276): unpinched bubbles are contiguities (|M| ≤ 3(n + r − 1)); pinched bubbles through ms-binary's bubble un-pinch Prop (consumed by name); hairs by kh-cckw's `SurgeryHairOpening`; cutting sides and the other long transitions by hull-euler's Euler lemma.
  - Feeds clause (a) of `OsinLemma94ClassEndLoopsInput` through ms-binary's `OsinLemma94ClassEndLoopsBudgetInput` (68b6b0e96). The class count from end loops is ct-bilateral-cell's and is not duplicated here.
  - Every new Prop is model-tested before it is consumed.
  - Ownership check at origin bbe90003a: the only user is `osinLemma94KindTransitionInput_of_longTransitions`; no shared-tree draft; sec5-sentences' .files equal origin.

## Duplicate `cuttingSides` in OsinLemma94ClassTransitions (main's item, 21:22)

- `OsinLemma94ClassTransitions` (sec5-sentences, down) and `OsinLemma94CuttingSides` both declared `OsinLemma94RealizedPolygons.cuttingSides` with the same body, so no root build could import both.
- Fix: ClassTransitions imports `OsinLemma94CuttingSides`, and the local copy is deleted; no statement changed.
- **LANDED 013a2dc59** (probe 0913-213117-20108 GREEN, BUILT, 0 sorryAx/error lines). The attic copy is ff0f63e83. The tag and SHA went to ms-core-5.

## Resumed 21:22 and 23:12: ClassTransitions fix, long-transition split

- **Duplicate `cuttingSides` fixed, LANDED 013a2dc59** (probe 0913-213117-20108 GREEN, BUILT, 0 sorryAx/error lines). `OsinLemma94ClassTransitions` imports `OsinLemma94CuttingSides` and drops its identical local copy. The tag went to ms-core-5.
- **Interface agreed with ms-binary (23:1x)**, who now owns `OsinLemma94ClassJoins`. I deliver `OsinLemma94LongTransitionInput` as declared. ms-binary consumes `osinLemma94KindTransitionInput_of_longTransitions` and keeps the bad junctions, cutting classes and budget ⊆ relator. Extra premises of my proof go into my producer theorem; the Prop does not change.
- **LANDED 51687cf4b, `Estimating/OsinLemma94LongTransitions`** (probe 0913-232345-17681 GREEN, BUILT, 0 sorryAx/error lines). Queued for wiring.
  - `contactTransitions` (next side a cell or boundary side) and `cuttingTransitions` (next side cutting); `kind_ne_next_of_mem_longTransitions`, `next_kind_of_mem_contactTransitions`, `card_longTransitions_le`, `sum_card_longTransitions_le`.
  - Named pieces `OsinLemma94ContactTransitionInput` and `OsinLemma94CuttingTransitionInput` (binders of the Prop), with hand model tests in their docstrings.
  - `osinLemma94LongTransitionInput_of_pieces` (constant K₁ + K₂). **This is a reduction, not a discharge. Both pieces are open.**
- Open pieces, owner ms-compress-1:
  1. Contacts. Euler on the planar object graph; no empty two-gons by `false_of_avoided_singleton` (unpinched bubble) or `PinchSplit.pinchSplitAbsorption` (pinched). First sub-lemma in progress: a two-side cell–cell polygon with no internal dart contradicts maximality (`ContiguityGeometry.ofSingletonFace` with empty sides, `targetBoundaryDarts (some j) = reverseDarts`, `inner_face` for the value).
  2. Cutting transitions. An entry marks a hole of the polygon that holds an object. `OsinLemma94CuttingSidesCount` bounds sides by entries, not entries by n, so this is new.

## Contact piece, first bricks (09-14 ~00:4x)

- **Split with ms-intro-2 (00:5x, their message).** ms-intro-2 proves `OsinLemma94CuttingTransitionInput` (CLAIM 318cd7abe) in new modules `Estimating/OsinLemma94CuttingTransitions*`. Route:
  - transitions ≤ same-face starts;
  - starts ≤ 2(e − v₀);
  - Euler on the first-return restriction with a hitting set, giving e − v₀ ≤ 2n;
  - K = 4.
  It publishes `CombMapEulerHittingSet` and `CombMapFirstReturnCounts`. I keep `OsinLemma94ContactTransitionInput`. Neither lane edits the other's modules.
- CLAIM two-sided bubble exclusions GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ContactBubble.lean
- **LANDED 92b271c3b** (probe 0914-012859-82927 GREEN, BUILT). Queued for wiring. It imports `OsinLemma94LongTransitions` and `SurgeryPinchSplitAbsorption`.
  - `face_value`: the face of a polygon reads a word of value one, through `DiscDiagram.inner_face` and `face_not_cell`.
  - `false_of_twoCellSides`: no polygon has exactly two sides, along two different relator cells. The face is a singleton contiguity region with empty sides (`ContiguityGeometry.ofSingletonFace`) that no selected region contains, so `false_of_avoided_singleton` applies.
  - `false_of_cellBoundarySides`: the same with the second side along one section of `∂Δ`. The bounds from `boundary_arc` are exactly the bounds `TargetsSectionIndex` asks for.
  - `false_of_boundaryCellSides`: the section side first, re-based by `List.rotate_rotate` and `List.rotate_append_length_eq`.
- Probe history:
  - 0914-00xx and ~00:45: MSI master down (infra); watcher probed once `ssh -O check` succeeded.
  - 0914-003538-8619: red. In the two-cell `hwalk`, `targetBoundaryDarts (some j)` reads `arc.reverseDarts` over the cycle `targetDarts (some j)`, definitionally but not syntactically equal to `cellDarts j`, so `simp` left the goal. Fixed with `simp only [List.append_nil]; rfl`.
- Still open for the contact count: the Euler count itself (candidate tooling: ms-intro-2's `CombMapEulerHittingSet`), and pinched bubbles through `PinchSplit.pinchSplitAbsorption`.
- Design notes for the Euler count of piece 1 (object multigraph D; degenerate faces and their exclusions): lane scratch `contact-euler-design.md`.

## Contact piece: Route C and piece J (09-14 08:4x–, after the reboot)

- Resume checks at origin f338faeb5: ContactBubble, LongTransitions and the report on disk equal origin. `.files` re-registered (clone lix-b). Nothing in flight.
- **Route C for `OsinLemma94ContactTransitionInput`.** On the walk of a relator polygon f, collapse the cell and boundary sides into letters (one letter per cell, one letter O for ∂Δ). A contact transition is a letter change. The count has four parts.
  1. **J.** No a…b…a…b along one face of a planar map. A cyclic word with no equal neighbours and no abab over d letters has length ≤ 2d − 2, so #changes_f ≤ 2d_f − 2.
  2. **Section corners.** Boundary j → j′ sits at a cut position, at most 5.
  3. **B.** Polygons with d_f ≥ 3: planar bipartite bound against {cells, O}, so Σ d_f ≤ 6(n + 1).
  4. **T.** Polygons with d_f = 2: planar multigraph on n + 1 vertices, no empty two-gon. An empty two-gon is a bubble, possibly with regions or pinches inside, excluded by ContactBubble, `pinchSplitAbsorption`, and a region merge still to write.
  - Total ≤ 36n. Regions, lobes and hairs need nothing: a letter never follows itself.
- CLAIM piece J GroupApproximation/GGT/VanKampen/CombMapNeighbourFacesNoninterleaving.lean
- **LANDED 1fd377b90** (probe 0914-084859-90205 GREEN, BUILT).
  - `NeighbourFaces.false_of_interleave`: interleaving neighbour faces a, b ≠ f, a ≠ b contradict planarity.
  - Proof: split the vertex at x₀ (`PinchSplit`, planar, all darts kept), merging a into f. The edge of the second a side is then a same-face edge, hence a bridge (`AvoidEdgeStep.not_eqvGen_alpha_of_sameFace`). Its two darts are joined avoiding it: along f, through the split into a, and across b.
  - Closed endpoint `neighbourFacesNoninterleaving : NeighbourFacesNoninterleavingStatement`, with position 0 the first a side. Rebasing to general positions is a corollary to add when the consumer needs it.
- Open: B (planar bipartite bound), T (empty two-gons), and the assembly into `OsinLemma94ContactTransitionInput`.
  - First probe 0914-084206-68298 red: `Equiv.Perm.inv_apply_self` is not at the pin, and a `← pow_add` rewrite missed after `simp only`. Fixed with the existing `faceOf_facePerm_pow` and `facePerm_pow_apply_pow`.
- CLAIM small-face Euler budget GroupApproximation/GGT/VanKampen/CombMapEulerSmallFaceBudget.lean
- **LANDED 0d3b600d9** (probe 0914-084522-79244 GREEN, BUILT, 0 sorryAx/error lines). `CombMap.six_mul_faceCount_le`: 6F ≤ 2E + 2t. `CombMap.two_mul_edgeCount_add_six_le`: 2E + 6 ≤ 3V + t on planar maps with every face of degree ≥ 4, where t counts the faces of degree < 6. Sharp on the square.
- Next, B and T combined: the bipartite polygon–object map H (a predicate restriction of the dual, one dart per (polygon, object) pair) with all faces of degree ≥ 4 and the budget applied per component. Degree-4 faces either hold a cell (t ≤ n) or are empty two-gons, excluded by ContactBubble, `pinchSplitAbsorption` and a region merge. Open question: planarity per component, through an IsRestriction for `CombMap.restrict`.
