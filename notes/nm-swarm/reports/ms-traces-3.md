# Lane ms-traces-3: tex 1977–2106 (prop:clifford-self-embedding, prop:clifford-locally-rf, the HS remark, the concrete instance, proof of thm:amenable-trace)

Wave-2 range lane of session nonsofic-existence-49. Manuscript at origin/main 5b3910136 (tex unchanged since 68481e4d7).

## CLAIM
- CLAIM general-W HS remark carriers (rows 86d7bbda9474, 42ae3f886537) GroupApproximation/Sofic/CliffordWitnessHSRemarkGeneral.lean

## Method
- Rows come from `metadata/NON_MF_SENTENCE_CENSUS.tsv`, matched by text. The census lines are at the pre-chain-core hash; current tex line = census line + 485.
- Every carrier module was checked against the import closure of `GroupApproximation.lean` at origin (6530 modules). All are reachable.
- `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` has no finding on any carrier here.
- No `sorry`/`admit`/`axiom`/`native_decide` token in the six sentence modules.
- Every sentence of tex 1977–2106 has a row. No unassigned sentence.

## Endpoints
- `CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF` and `manuscriptMapSignEqOneOfIsOperatorMFTarget`: for every countable Kazhdan Γ, injective α and a ∉ range α. `#audit_closed_axioms` in Audit/Intro, Audit/Sec2 and Audit/Sec4.
- `Ambient α hα = CliffordLamp (Vertical α hα ⧸ Γ) ⋊ Vertical α hα` (MarkedCompressionGroup:56/217/278), with Vertical the ascending HNN extension. This is the printed W.
- `AmenableTraceTheorem.manuscriptCliffordLocallyRF`: all printed clauses (W ≅ W₀ ⋊ ℤ, W₀ locally RF, sofic, not MF, QD trace on W₀, amenable and not QD on W), at the printed hypotheses. Closed-audited.
- Concrete instance: `gammaBar_residuallyFinite`, `gammaBar_hasKazhdanPropertyT`, `printedConjDDoublesTranslation`, `printedConjDRangeEvenTranslations` (injective, even translations, index 8), `manuscriptAffineCliffordHypotheses` (index 8, v₁ ∉ range α), `manuscriptSentence_theorem4Application`. Closed-audited.

## Literature inputs used in this range
- Elek–Szabó Thm 1: proved, `SoficByAmenablePermanence.manuscriptSoficOfSoficKerOfAmenableQuotient` (sofic kernel plus amenable quotient ⇒ sofic) together with `isSofic_of_every_finset_mem_sofic_subgroup` and `isSofic_of_increasing_union`.
- BHV Example 1.7.4(i), (T) for ℤ³ ⋊ SL₃(ℤ): proved, `gammaBar_hasKazhdanPropertyT` (closed audit).
- thm:compression-criterion is internal: `manuscriptOneSidedCompressionCriterion` (range of ms-compress-4).

## Verdicts
| key | tex line | status | carriers | verdict |
|---|---|---|---|---|
| `8abb5071b65b` | 1979 | formalized | CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF | PASS |
| `7732f82e8623` | 1979 | formalized | CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget | PASS |
| `177456a78260` | 1986 | formalized | AmenableTraceSentencesB.manuscriptSentence_rootLampCentralizesFixesCoset | PASS |
| `a0acefd07ec1` | 1986 | formalized | CliffordConstructionSentences.manuscriptSentence_conjugatedLampsAtCosets | PASS |
| `dba28fb94e6d` | 1986 | formalized | CliffordConstructionSentences.manuscriptSentence_movedCosetsDistinct AmenableTraceSentencesB.manuscriptSentence_distinctInvolutionsCommutatorSign | PASS |
| `91502a70ae59` | 1986 | formalized | AmenableTraceSentencesB.manuscriptSentence_defectFactorization CliffordWitnessDirectDefect.pointDefect_mem_printedDefect CliffordWitnessDirectDefect.stable_mem_compressionSet CliffordWitnessDirectDefect.lamp_mem_centralizer | PASS |
| `b33af3eb4b3c` | 1986 | formalized | CliffordWitnessDirectDefect.signSubgroup_le_printedDefect | PASS |
| `24b5330b38b0` | 1986 | formalized | AmenableTraceSentencesB.manuscriptSentence_signSubgroupCentralNormalFiniteHasT | PASS |
| `013d2e0e8b4a` | 1986 | formalized | CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget | PASS |
| `28740c0c5a93` | 1986 | formalized | CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF | PASS |
| `a2ba60db6a3b` | 2006 | formalized | AmenableTraceTheorem.manuscriptCliffordLocallyRF CliffordWitnessLocallyRFByInt.manuscriptAmbientEquivShiftKernelForByInt CliffordWitnessLocallyRFByInt.manuscriptShiftKernelForIsLocallyResiduallyFinite | PASS |
| `b48122a6b07d` | 2006 | structural | — | PASS (honest structural) |
| `93aa71e6b818` | 2012 | formalized | AmenableTraceTheorem.manuscriptCliffordLocallyRF | PASS |
| `a0abcf4e0a16` | 2012 | formalized | AmenableTraceTheorem.manuscriptCliffordLocallyRF | PASS |
| `9355c08e7f2b` | 2019 | formalized | CliffordWitnessLocallyRFByInt.witnessGroupEquivShiftKernelByInt AmenableTraceTheorem.manuscriptSentence_reassociation | PASS |
| `bc2d73bb124a` | 2024 | definition | MappingTelescope.level MappingTelescopeFiniteOrbits.verticalLevel | PASS |
| `4cdae54eba21` | 2024 | formalized | AmenableTraceTheorem.manuscriptSentence_commensuration MappingTelescopeFiniteOrbits.t_conj_base_eq_compressed | PASS |
| `404ff3b063bf` | 2024 | formalized | AmenableTraceTheorem.manuscriptSentence_stabilizerAndOrbitFinite | PASS |
| `edc038ff7b5f` | 2033 | formalized | AmenableTraceTheorem.manuscriptSentence_finiteSubsetOneLevel | PASS |
| `e4ebdec3bbab` | 2033 | definition | AmenableTraceTheorem.manuscriptSentence_finiteInvariantSubgroup | PASS |
| `a60285a8682e` | 2033 | formalized | AmenableTraceTheorem.manuscriptSentence_finiteInvariantSubgroup | PASS |
| `2a24a52c111f` | 2040 | formalized | AmenableTraceTheorem.manuscriptSentence_finiteInvariantSubgroup | PASS |
| `675969466d3b` | 2040 | formalized | AmenableTraceTheorem.manuscriptSentence_semidirectResiduallyFinite | PASS |
| `9f522f4b56dd` | 2040 | formalized | AmenableTraceTheorem.manuscriptSentence_semidirectResiduallyFinite | PASS |
| `ab3b4185d7d4` | 2040 | formalized | AmenableTraceTheorem.manuscriptSentence_semidirectResiduallyFinite | PASS |
| `bba6a4ecce85` | 2040 | formalized | AmenableTraceTheorem.manuscriptSentence_semidirectResiduallyFinite | PASS |
| `508294d77cb5` | 2040 | formalized | AmenableTraceTheorem.manuscriptSentence_locallyResiduallyFinite AmenableTraceTheorem.manuscriptSentence_fgSubgroupSofic | PASS |
| `8cde0b44b52f` | 2051 | formalized | AmenableTraceTheorem.manuscriptSentence_quotientAmenable | PASS |
| `2c614717a212` | 2051 | formalized | isSofic_of_every_finset_mem_sofic_subgroup isSofic_of_increasing_union SoficByAmenablePermanence.manuscriptSoficOfSoficKerOfAmenableQuotient AmenableTraceTheorem.manuscriptSentence_wSoficMechanism | PASS |
| `f1f1ba4ba319` | 2051 | formalized | AmenableTraceTheorem.manuscriptSentence_notMF | PASS |
| `a998ccfa2015` | 2051 | formalized | AmenableTraceTheorem.manuscriptSentence_traceConclusions | PASS |
| `b7a852f284f1` | 2062 | structural | — | PASS (honest structural) |
| `86d7bbda9474` | 2062 | formalized | CliffordWitnessHSRemark.manuscriptSentence_soficPermutationModelsHS CliffordWitnessHSRemark.tendsto_hsNorm_modelUnitary_mul CliffordWitnessHSRemark.tendsto_hsNorm_modelUnitary_sub_one CliffordWitnessHSRemark.tendsto_movedFraction_of_ne_one | GAP: carried only at the concrete instance `WitnessGroup`, not for the general W of prop:clifford-locally-rf; fix claimed above |
| `42ae3f886537` | 2062 | formalized | CliffordWitnessHSRemark.manuscriptSentence_hsCollapseFails CliffordWitnessHSRemark.manuscriptSentence_noSoficCompressionCriterion | GAP: carried only at the concrete instance `WitnessGroup`, not for the general W of prop:clifford-locally-rf; fix claimed above |
| `3229365c29c6` | 2074 | definition | ExplicitLinearModel.gammaBar AffineHNNBase.affUnit AffineHNNBase.affUnit_val Manuscript.NonMF.AffineDoublingLiteralModel.PrintedGammaBarAffine Manuscript.NonMF.AffineDoublingLiteralModel.printedGammaBarAffine | PASS |
| `77028123cdd6` | 2083 | formalized | ExplicitIntegralLinearModel.gammaBar_residuallyFinite CommutingLampCollapse.gammaBar_hasKazhdanPropertyT | PASS |
| `e947a3d4f4a1` | 2083 | definition | ExplicitLinearModel.dU ExplicitLinearModel.conjD Manuscript.NonMF.AffineDoublingLiteralModel.PrintedConjDDefinition Manuscript.NonMF.AffineDoublingLiteralModel.printedConjDDefinition | PASS |
| `80c65e0771e4` | 2093 | formalized | Manuscript.NonMF.AffineDoublingLiteralModel.PrintedConjDDoublesTranslation Manuscript.NonMF.AffineDoublingLiteralModel.printedConjDDoublesTranslation | PASS |
| `c48c7da870a2` | 2093 | formalized | Manuscript.NonMF.AffineDoublingLiteralModel.PrintedConjDRangeEvenTranslations Manuscript.NonMF.AffineDoublingLiteralModel.printedConjDRangeEvenTranslations | PASS |
| `8c17c33ec225` | 2093 | formalized | AmenableTraceSentencesB.manuscriptSentence_concreteInstanceDoubling AmenableTraceTheorem.manuscriptAffineCliffordHypotheses | PASS |
| `7f667d9f1cb7` | 2093 | formalized | AmenableTraceTheorem.manuscriptAffineCliffordConclusions AmenableTraceTheorem.manuscriptSentence_theorem4Application | PASS |
| `4ce81a3db24b` | 2100 | formalized | AmenableTraceTheorem.manuscriptSentence_theorem4Application | PASS |
