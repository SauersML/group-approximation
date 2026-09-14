# Lane ms-core-2: sentence ledger for lem:chain-core-models (tex 1371–1458)

Lead: session nonsofic-existence-49 (wave 2, Brief C; see `notes/nm-swarm/reports/ct-lead.md`).
Snapshot: origin/main e1cce5941 (09-13 16:39). The tex range is byte-identical to 68481e4d7.

## Summary

- The range holds 48 census keys (census merge `merge-0913-160921`, grouped by the older tex lines 1370–1454).
- Every key has an owner in the other swarm: chain-words, chain-subshift, chain-itinerary, hull-euler (S2) or chain-core
  (S1). No unowned leaf is left in this range, so this lane builds no carrier here.
- A hand check of every printed step found no false claim (section "Hand audit" below).
- This lane's own work in the range is one model test of the symbolic-core definitions (claim below).

## CLAIM

CLAIM model test: step-subshift calibration of `IsCyclicEdge`, `CycleCondition`, `coreSubshift`,
`reachableCylinderUnion` and `shift_mem_diff_of_not_isCyclicEdge` —
`GroupApproximation/Dynamics/StepSubshiftCoreCalibration.lean`
LANDED 66a51b0eb (probe 0913-172335-49867 GREEN, BUILT); queued for wiring. Results: the edge `false → true`
is not cyclic, the cycle condition fails, `coreSubshift` is exactly the two constant configurations,
`shift_mem_diff_of_not_isCyclicEdge` fires on the step point, and the reachable cylinder union from `true` is
`{x | x 0 = true}`. It is a model test, not a carrier, so it has no census rows.

CLAIM (09-13 ~18:30, main's item: `CoreModelsLEFStatement`, "R_Y is LEF"; successor to chain-itinerary's general-X route)
- `GroupApproximation/Dynamics/ChainCoreGeneralFactor.lean`: the factor maps `π_m : Y_* → π_m(Y_*)`, the shift on
  `π_m(Y_*)`, pullback injective along surjective factor maps, and increasing pullback ranges.
- `GroupApproximation/Dynamics/ChainCoreGeneralLEF.lean`: `R_{Y_*}` LEF for `Y_* = generalCore T S`. Pullback along
  `π_m : Y_* → π_m(Y_*)` is injective, the ranges increase, and every element lies in some range. The symbolic inputs
  are hypotheses: `CycleCondition (itineraryCore T (S l))` and the cycle-condition LEF theorem.
- `GroupApproximation/Dynamics/ChainCoreGeneralRecurrent.lean`: `generalCore T S = chainRecurrentSet T`.
- `GroupApproximation/Manuscript/NonMFSentences/CoreModelsLEF.lean`: `coreModelsLEFStatement : CoreModelsLEFStatement`.
- Boundary agreed by message with ms-traces-3 (symbolic side). It adopts chain-words' unlanded SubshiftFiniteWindow and
  SubshiftCycleLEF, `cycleCondition_coreSubshift`, the Z_r cycle condition, and nonemptiness.
- Dead-lane audit at origin a568a49a1: chain-itinerary and chain-subshift have no unlanded bytes. chain-words holds
  SubshiftFiniteWindow (md5 97ff5d23) and SubshiftCycleLEF (md5 dbc679f8), unlanded with no green record; they go to
  ms-traces-3.

## Ledger

Status: `landed` means a carrier is on origin (unwired unless noted); `planned` means named in the owner's report only.

### Statement (tex 1372–1376)

| key | tex | sentence | owner | carriers | status |
|---|---|---|---|---|---|
| `d8e1a694d87c` | 1372 | Y nonempty, closed, invariant; R_Y LEF | hull-euler (closed, invariant); chain-itinerary (nonempty, LEF) | `Dynamics.isClosed_chainRecurrentSet`, `image_chainRecurrentSet` (20911e5b2); `chainRecurrentSet_nonempty`, `isLEFRing_crossedProduct_chainRecurrentSet` planned | partial |
| `0ae6fc9e199c` | 1373 | X∖Y covered by translates of P∖T(P), P clopen, T(P) ⊆ P | hull-euler (ruling 16:17: direct atom-graph module) | `compl_chainRecurrentSet_subset`, closed endpoint `printedChainCoreCovering` (ChainRecurrenceCovering 5b63c946c) | landed |
| `73bd8ac910aa` | 1375 | each such set is wandering | hull-euler (S2) | `isWandering_diff_image`, inside `printedChainCoreCovering` (5b63c946c) | landed |

### Subshift case: word graphs and LEF models (tex 1380–1400), chain-words

| key | tex | sentence | carriers | status |
|---|---|---|---|---|
| `53fd5ea7d3d0` | 1380 | suppose X is a subshift over a finite alphabet | hypotheses `hXc`, `hX` | landed |
| `9bc3873fb872` | 1381 | word graph at level r | `WordGraph.word`, `language`, `wordEdge`, `wordGraph` (7c770d047) | landed |
| `078684fc2a60` | 1383 | cyclic edge; cycle condition | `WordGraph.IsCyclicEdge`, `CycleCondition` (7c770d047) | landed |
| `dfc6d4510272` | 1386 | cycle condition ⇒ LEF crossed product | `isLEFRing_skewMonoidAlgebra_of_cycleCondition` (SubshiftCycleLEF) | planned |
| `8bf7f40918d5` | 1387 | finite table, Laurent form, window | `exists_radius` (SubshiftCycleLEF) | planned |
| `56b6a80cc911` | 1390 | high level, cycles containing witness words | `exists_periodicModels_of_cycleCondition` | planned |
| `2ed7f807a3a6` | 1392 | reading cycles gives periodic models | `exists_periodic_of_isCyclicEdge` (SubshiftCyclePeriodic 6078315b6) | landed |
| `57cd1b63930c` | 1394 | repeat each cycle past twice the Laurent degree | `exists_periodicModels_of_cycleCondition` | planned |
| `0941296cf395` | 1395 | diagonal coefficients, cyclic shift for u | `Pestov91.periodicModel`, `shiftMatrix` | landed (consumed) |
| `4aede6d48b4d` | 1397 | windows preserve products and sums; witnesses separate | `evalFamily` | planned |
| `b94a006ee638` | 1399 | the product is the finite model | inside `isLEFRing_skewMonoidAlgebra_of_cycleCondition` | planned |
| `533771f4f22d` | 1400 | periodic models need not lie in the subshift | periodic word not asked to lie in X | planned |

### Retained subshifts, the core, Y_0 = CR(T), noncyclic edges (tex 1402–1426), chain-subshift

| key | tex | sentence | carriers | status |
|---|---|---|---|---|
| `9ea50b0ff631` | 1402 | retain cyclic edges; Z_r | `ChainCore.retainedSubshift` (dbb102249) | landed |
| `cbf45b0e1c51` | 1404 | finite retained paths extend to periodic paths | waits on SubshiftCyclePeriodic | planned |
| `1d52a79f1fef` | 1405 | Z_r has dense periodic points and the cycle condition | `cycleCondition_retainedSubshift` | planned |
| `f7c8d8aab016` | 1406 | Z_r nonempty; Z_{r+1} ⊆ Z_r | `retainedSubshift_succ_subset` (dbb102249); nonempty planned | partial |
| `b39310f67614` | 1408 | Y_0 = ⋂ Z_r | `ChainCore.coreSubshift` (dbb102249) | landed |
| `ded9e9646e4b` | 1408 | Y_0 nonempty; Y_0 ⊆ X | `coreSubshift_subset` (dbb102249); nonempty planned | partial |
| `758517bf8d56` | 1410 | languages stabilize | `exists_language_retainedSubshift_eq` (dbb102249), `exists_restrict_image_eq_of_antitone` (239b3a4ca) | landed |
| `647f44a95b8a` | 1411 | Y_0 has the cycle condition | `cycleCondition_coreSubshift` | planned |
| `ffa61d258258` | 1412 | characterization of Y_0 | `mem_coreSubshift_iff` (dbb102249) | landed |
| `048953d87f92` | 1415 | closed approximate orbits give closed walks | `reflTransGen_word_of_transGen` (CoreSubshiftChainRecurrent b34b97bfe) | landed |
| `ae9c3d8b9922` | 1416 | cycles give closed approximate orbits | `transGen_of_reflTransGen` (b34b97bfe) | landed |
| `4fc54b29a740` | 1419 | overlap gives the accuracy | `windowRel`, `exists_windowRel_subset`, `chainStep_windowRel_iff` (b34b97bfe) | landed |
| `a08f25fce44c` | 1420 | Y_0 = CR(T) | `isChainRecurrent_iff_mem_coreSubshift`, `coreSubshift_eq_chainRecurrentSet`, `isMetricChainRecurrent_iff_mem_coreSubshift` (b34b97bfe) | landed |
| `d8f8d764406c` | 1422 | noncyclic edge ⇒ forward-closed set excluding a | `not_reflTransGen_of_not_isCyclicEdge`, `reachableCylinderUnion` (dbb102249) | landed |
| `9c49a2efb0ca` | 1424 | T(P) ⊆ P | `mapsTo_shift_reachableCylinderUnion` (dbb102249) | landed |
| `854ec7cb0423` | 1424 | Tx ∈ P∖T(P) | `shift_mem_diff_of_not_isCyclicEdge` (dbb102249) | landed |
| `3ef2a7cdb9bd` | 1425 | defects wandering by nesting | hull-euler (S2): `isWandering_diff_image` (5b63c946c) | landed |

### General X (tex 1428–1458), chain-itinerary (plus hull-euler, chain-core)

| key | tex | sentence | owner | carriers | status |
|---|---|---|---|---|---|
| `3d8a2204752a` | 1428 | refining clopen partitions, mesh → 0 | chain-itinerary | `ChainCore.exists_refiningClopenPartitions` (3d9b2c4f0) | landed |
| `fe2bd83087c0` | 1429 | itinerary subshifts π_m, cores Y_m, one-block factors ρ_lm | chain-itinerary | `itinerary`, `itinerarySubshift`, `oneBlock` (d616d6bcb) | landed |
| `4bb19e581840` | 1432 | one-block maps preserve the cycle condition | chain-itinerary | `cycleCondition_image_comp`, `cycleCondition_oneBlock_image`, `oneBlock_image_itineraryCore_subset` (OneBlockCycleCondition dd08aab94) | landed |
| `ed348643e2ad` | 1434 | ρ_lm(Y_l) ⊆ Y_m; the display for Y_* | chain-itinerary | `inverseLimitCore`, `preimage_itinerary_antitone` (61363f1b9) | landed |
| `807793f12a5e` | 1439 | π_m(Y_*) = ⋂ ρ_lm(Y_l) by fibre compactness | chain-itinerary | `itinerary_image_inverseLimitCore` (61363f1b9) | landed |
| `b180421b55ab` | 1440 | the intersection has the cycle condition | chain-itinerary | `cycleCondition_iInter_oneBlock_image`, `cycleCondition_itinerary_image_generalCore` (ItineraryCoreCycleCondition dd08aab94) | landed |
| `2df08eeac3cb` | 1442 | coefficient pullback injective unital; fine partitions | chain-itinerary | `CrossedProduct.coeffMap_injective` (f9390d923), `exists_forall_proj_eq_imp_of_locallyConstant` (3d9b2c4f0) | landed |
| `c825bc73828a` | 1444 | R_{Y_*} increasing union of LEF rings | chain-itinerary | `isLEFRing_of_monotone_ringHom_range` (6ac372c36); `isLEFRing_crossedProduct_generalCore` planned | partial |
| `c99bf0bdb029` | 1447 | chain recurrence passes to factors, so Y ⊆ Y_* | hull-euler | `Dynamics.mapsTo_chainRecurrentSet` (20911e5b2) | landed |
| `e6626f95fede` | 1448 | x ∈ Y_*, mesh below ε | chain-itinerary | `generalCore_subset_chainRecurrentSet` | planned |
| `2583cbd0c0f2` | 1449 | an accurate closed chain matches symbols | chain-itinerary | same | planned |
| `3b218f92cd81` | 1451 | lift intermediate points with fixed endpoints | chain-itinerary | same | planned |
| `fb195144e5c2` | 1453 | consecutive lifts lie in one atom | chain-itinerary | same | planned |
| `8921296d639a` | 1454 | Y_* = Y | chain-itinerary | `generalCore_eq_chainRecurrentSet` | planned |
| `042966c81c7e` | 1456 | pulled-back symbolic defects cover X∖Y | chain-itinerary | `exists_defect_translate_of_not_mem_chainRecurrentSet` | planned |
| `549aa93e832f` | 1457 | they avoid Y; set p, d and calculate | chain-core (S1) | `ClopenCrossedProduct.defectP`, `defectD`, `map_defectD_eq_zero` (32275d037), `ClopenDefectRestriction` (a55be3025) | landed |

## Hand audit of the printed steps

No false claim found. Each item gives the check.

1. **Definitions match the print.** `IsCyclicEdge` asks for a path from the suffix back to the prefix; `ReflTransGen` admits the
   loop, as "lies on a directed cycle" does. `CycleCondition` quantifies over every level, including `r = 0` (`isCyclicEdge_zero`).
   `retainedSubshift` asks every window to be a retained edge, which is "read from bi-infinite paths". `mem_coreSubshift_iff`
   is the sentence at tex 1412.
2. **Z_r has the cycle condition.** A retained edge lies in one strongly connected component of the level-r graph of X, and every
   edge inside a component is cyclic. So a finite retained path stays inside one component and closes up, which gives dense
   periodic points and the cycle condition at every level. Nonemptiness uses that X is nonempty (tex 1345): a finite graph in which
   every vertex has an out-edge has a cycle.
3. **Z_{r+1} ⊆ Z_r.** Projecting a level-(r+1) cycle gives closed walks through both level-r subwords of an edge.
4. **Y_0 = CR(T).** Forward: an entourage chain accurate on [−N, N] makes the words x_k[i, i+r) a closed walk through the edge
   x[i, i+r] (at least one step, as `TransGen` requires). Converse: realize the edges of a cycle through x[−N, N+1] by points of X,
   with x first and last; consecutive points agree after shifting on [−N, N−1].
5. **Noncyclic edge.** b cannot reach a, T(P) ⊆ P and Tx ∈ P∖T(P) are the landed green theorems above. "Wandering by nesting" holds
   for a homeomorphism, since T^{j+1}P ⊆ T^j P for every j ∈ ℤ.
6. **General X.** A one-block image of a cycle-condition subshift has the cycle condition, since a closed walk maps to a closed walk.
   A cycle-condition subshift Z ⊆ X_m lies in the core, because a closed walk in the graph of Z is one in the graph of X_m; so
   ρ_lm(Y_l) ⊆ Y_m. Fibre compactness gives π_m(Y_*) = ⋂_{l≥m} ρ_lm(Y_l): the sets π_m⁻¹(y) ∩ π_l⁻¹(Y_l) are closed, nonempty and
   decreasing.
7. **Increasing union.** Nesting of the pulled-back rings needs ρ_lm ∘ π_l = π_m (`oneBlock_itinerary`). A locally constant function
   on compact Y_* is uniformly locally constant, so it factors through some π_m.
8. **Y_* ⊆ Y.** Accuracy (shift y_i)_0 = (y_{i+1})_0 puts T x_i and x_{i+1} in one atom of P_m, whose diameter is below ε.
9. **Covering.** A noncyclic window of π_m(x) at position i gives T^{i+1}x ∈ π_m⁻¹(P)∖T(π_m⁻¹(P)), and π_m⁻¹(P) is clopen with
   T(π_m⁻¹P) ⊆ π_m⁻¹P.

## Watch items (for the owners, relayed through main)

- W1, fibre compactness (`807793f12a5e`): RESOLVED. The argument needs X_l to be the image π_l(X), and origin defines
  `itinerarySubshift T S := Set.range (itinerary T S)`.
- W2, two routes for the covering: the statement sentence `0ae6fc9e199c` is carried by hull-euler's direct atom-graph module, while
  the printed proof route is the pullback of symbolic defects (`042966c81c7e`, chain-itinerary, planned). Grade the proof sentences
  against the pullback route.
- W3, wandering: RESOLVED. hull-euler's `isWandering_diff_image` (ChainRecurrenceCovering 5b63c946c) carries `73bd8ac910aa` and
  `3ef2a7cdb9bd`.

## Progress log

- 09-13 ~17:05: ledger and claim landed (7a29fbdf0).
- 09-13 ~17:15: W1 and W3 resolved against origin; StepSubshiftCoreCalibration probing.
- 09-13 ~17:30: after the lead restart, two red probes (an unused closedness lemma; `norm_num` not imported) were fixed.
  StepSubshiftCoreCalibration GREEN 0913-172335-49867, LANDED 66a51b0eb, queued for wiring. Ledger refreshed against
  b34b97bfe (Y_0 = CR(T)) and dd08aab94 (one-block cycle condition, intersection cycle condition). Still planned by owners:
  the cycle-condition LEF theorem (chain-words), nonemptiness and the cycle condition of Z_r and Y_0 (chain-subshift),
  `R_{Y_*}` LEF, `Y_* = Y`, the defect cover and `R_Y` LEF (chain-itinerary).
- 09-13 ~17:55: main assigned help on W1 binder 8 (`GeodesicCollarStatement`, reduced to `StripStepStatement`). No leaf was
  taken: w1-binder-8 already holds the whole step, pinch merge, doubling half and endpoints `stripStepStatement_holds` /
  `geodesicCollarStatement_holds`, in `GGT/VanKampen/SurgeryGeodesicCollarStripStep.lean`. This lane created no module there.
  Leaf for binder 8: none.
- 09-13 ~18:55: general-X route LANDED 0bdeb7074 (probe 0913-184756-35974 GREEN: 4 BUILT, 0 sorryAx/error lines), queued for
  wiring. Modules:
  - `Dynamics/ChainCoreGeneralFactor`: `image_generalCore`, `coreFactor`, `coreFactorShift`, `coreFactorMap`
    (continuous, surjective, `coreFactorMap_semiconj`), `comap_injective`, `range_comap_coreFactorMap_mono`,
    `itinerary_apply_zero`.
  - `Dynamics/ChainCoreGeneralLEF`: `SubshiftCycleConditionLEFInput`, `exists_forall_proj_eq_imp_of_locallyConstant_subtype`,
    `exists_comap_coreFactorMap_eq`, `exists_mem_range_comap_coreFactorMap`, `isLEFRing_clopenCrossedProduct_generalCore`.
  - `Dynamics/ChainCoreGeneralRecurrent`: `discreteQuotientUniformSpace` (a local instance through `replaceTopology`),
    `chainRecurrentSet_subset_generalCore`, `generalCore_subset_chainRecurrentSet`, `generalCore_eq_chainRecurrentSet`.
  - `Manuscript/NonMFSentences/CoreModelsLEF`: `SubshiftCoreCycleConditionInput`, `isLEFRing_restrictHomeo_of_eq`,
    `coreModelsLEFStatement_of_inputs : SubshiftCycleConditionLEFInput → SubshiftCoreCycleConditionInput →
    DynamicRankBudget.CoreModelsLEFStatement`.
  - Residual for the closed endpoint: the two symbolic inputs (ms-traces-3). Drafts on disk:
    `WordGraph.isLEFRing_clopenCrossedProduct_of_cycleCondition` (SubshiftCycleLEF) and
    `ChainCore.cycleCondition_coreSubshift` (CoreSubshiftCycle). Both signatures match the inputs.
  - Census rows: `metadata/nm-census-rows/ms-core-2.tsv` (keys c825bc73828a, 2df08eeac3cb, e6626f95fede, 2583cbd0c0f2,
    3b218f92cd81, fb195144e5c2, 8921296d639a, d8e1a694d87c).
- 09-13 ~19:15: CLOSED ENDPOINT LANDED b7e521e57 (probe 0913-191003-38463 GREEN, BUILT, 0 sorryAx/error lines), queued for wiring.
  `Manuscript/NonMFSentences/CoreModelsLEFClosed`: `subshiftCycleConditionLEFInput`, `subshiftCoreCycleConditionInput`
  (discharged by ms-traces-3's 178808d0a) and `coreModelsLEFStatement : DynamicRankBudget.CoreModelsLEFStatement`, audited
  closed to propext, Classical.choice and Quot.sound. The first landing attempt hit push contention; the retry landed.
  Census: c825bc73828a is now formalized. d8e1a694d87c stays partial because its nonempty clause has no carrier here.
- 09-13 ~19:45: FIRST SENTENCE CLOSED, LANDED a28419dba (probe 0913-193800-96165 GREEN, BUILT, 0 sorryAx/error lines), queued
  for wiring. `Manuscript/NonMFSentences/ChainCoreModelsStatement`:
  - `itineraryCore_nonempty` and `generalCore_nonempty` (from `coreSubshift_nonempty`, ms-traces-3 178808d0a, and
    `inverseLimitCore_nonempty`);
  - `chainRecurrentSet_nonempty`, through `generalCore_eq_chainRecurrentSet`;
  - `PrintedChainCoreModelsFirstSentence` with `printedChainCoreModelsFirstSentence` (Y nonempty, closed, invariant, R_Y LEF),
    audited closed to propext, Classical.choice and Quot.sound.
  - Census: d8e1a694d87c is now formalized. This lane's scope is finished; main released it.
