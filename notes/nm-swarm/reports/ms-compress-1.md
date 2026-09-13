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

## For the census lane

- When the new carriers land, 629f562df6bc, 630db09c6f46 and daecb970c06a gain them. 5e9b44d1c0bb gains one if G4 finds a route gap.
- daecb970c06a should name the theorem `sentence_36cd63cf2803_isomorphism`, not the Prop.
