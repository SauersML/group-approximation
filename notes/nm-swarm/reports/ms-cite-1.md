# ms-cite-1: literature-input ledger for `non_mf_groups_exist.tex`, tex 1–1337

Lane `ms-cite-1` (session nonsofic-existence-49, wave 2), 2026-09-13. Tex at origin/main 835fa3ee5, whose tex
equals 68481e4d7.

## Method

- Every `\cite` in tex 1–1337 (47 citing sentences) was joined by sentence text to its row in
  `metadata/NON_MF_SENTENCE_MAP.tsv` through `metadata/NON_MF_SENTENCE_CENSUS.tsv`.
- Every carrier the row names was checked on origin/main:
  - root reachability: the import closure of `GroupApproximation.lean`, 6530 modules;
  - its audit lines, `#audit_closed_axioms` or `#audit_axioms` (one- and two-line forms, 9239 names);
  - the statement text of each carrier audited only with `#audit_axioms`.
- The carrier modules were scanned for the quarantined package names in `metadata/LITERATURE_QUARANTINE.md`.

## Verdict

- Every cited result that a proof in tex 1–1337 uses is PROVED in Lean: closed, root-reachable, no literature
  binder. There is one exception: **Hull's small cancellation theorem**, still assumed through the W1 wall on
  the thm:torsion-free rows (see "Still assumed").
- Census defect: row `b1b04e376fe7` names the wrong carriers. The correction is in
  `metadata/nm-census-rows/ms-cite-1.tsv`.
- Three formalized rows had carriers with binder-free statements but no closed audit.
  `Manuscript/NonMFSentences/CitationSweepIntroAudit.lean` adds `#audit_closed_axioms` for them (probe pending).

## Proof steps and asserted results

| tex | cite | row | carrier on main | verdict |
|---|---|---|---|---|
| 87–98 | CDE (MF group definition) | 88e8012cb87e formalized | `OneSidedMFRadical.manuscriptIntroductionMFDefinition` (closed) | proved |
| 98–102 | Korchagin Props 2, 7 | b1b04e376fe7 formalized | `NonMFSentences.KorchaginSentence.manuscriptSentence_korchaginFullSequenceSeparation : ∀ countable G, IsOperatorMF G ↔ Nonempty (WeakMFApproximation G)` (closed, root). **The map row names the strong-convergence carriers of the next sentence instead** | proved; row corrected |
| 102–105 | GaoEtAl, Schafhauser | 837b7cffa562 formalized | `not_isStronglyOperatorMF_of_not_isOperatorMF` (its only premise is the sentence's own) | proved |
| 115–116 | BK (MF algebra) | ad33e493e32f formalized | `manuscriptArbitraryPositiveDimensionAlgebraMFDefinition` (closed) | proved |
| 151–153 | Khanh–Thanh Prop 4.2, Cor 4.4 | 8766dc520cfb formalized | 3 of 3 carriers closed | proved |
| 273–274 | Elek–Szabó Thm 1 | f969236a73d8 formalized | `AmenableTraceTheorem.manuscriptWSoficFromLocallyRFExtension` (closed) | proved |
| 274–282 | Brown, STW (question), TWW | a96c09324a87 formalized | the used content "C*_max(W) is not nuclear" is `manuscriptSentence_maximalCStarWNotNuclear`; no proof consumes TWW | proved; TWW is context |
| 284–286 | Korchagin Cor 10, Prop 13 | 2a97fb901bad formalized | `manuscriptShiftKernelIsOperatorMF : IsOperatorMF ShiftKernel` via `isOperatorMF_of_isLEF`, `isLEF_of_locallyResiduallyFinite` | proved; closed audit added |
| 286–288 | Korchagin (question) | cd3ea932e46a formalized | `manuscriptMFNotClosedUnderIntSemidirect` (∃-statement) | proved; closed audit added |
| 321–325 | Lubotzky–Oppenheim, Thom | 6edef6dc2d68 formalized | `manuscriptSentence_positiveMFProblemAnswerMakesEveryCountableGroupMF` (closed, now root) | proved |
| 328–332 | MIPRE, Goldbring–Hart Prop 6.1, Rem 6.2 | abfcbcb3af2b formalized | `NonMF.PriorWork.printedNegativeConnesEmbeddingSentence`: the conclusion comes through the paper's reduced group algebra; the Connes-embedding route is credited context no proof consumes | proved; closed audit added |
| 464–466 | Akemann–Walter | 86ee71463acf definition | `manuscriptSentence_kazhdanProjection` (closed), `KazhdanData.projection` | proved |
| 518–520 | Akemann–Walter | 87f873612529 formalized | `TransportProjectionCommutation.exists_projectionData (KD : KazhdanData L)`; `KD` from `exists_kazhdanData` (root, from (T)) | proved |
| 752–753 | Akemann–Walter | 0546c4f445c0 definition | `KazhdanData.projection`, `StrictKazhdanCompression.proj/shift` | definition |
| 773–774 | BK (separable RFD ⇒ MF) | e4fcef4295ca formalized | `ResiduallyFiniteDimensionalMF.isMFAlgebra`, `MatrixCoronaFinite.mfAlgebra_isStablyFinite` (closed) | proved |
| 792–793 | Korchagin Cor 10 | 330d435b12e2 formalized | `manuscriptSentence_reductionModuloOddRFAndMF` (closed) | proved |
| 952–955 | EJZ Thm 1.1, BHV Thm 1.3.1 | 0939d33e1ff4 formalized | 4 of 4 closed; EJZ = `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` (via `ejz`); BHV = `KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT` | proved |
| 1065–1067 | EJZ | b45891d88426 formalized | closed carrier present | proved |
| 1098–1099 | EJZ | 057fe08fb3bb formalized | 2 of 2 closed | proved |
| 1160–1162 | GHW Thm 4 | b6d1590be7ab formalized | `GHW.printedGHWTheoremFour : ∀ field K, ∀ countable Γ ≤ GL_2(K), Haagerup` (closed, root) | proved at printed generality |
| 1169–1171 | EJZ | 3009704fef89 formalized | `EJZCitationSentences.manuscriptSentence_jacobsonThreeCoordinatesCarryPropertyT` (closed, two-line audit) | proved |
| 1179–1181 | Khanh–Thanh Prop 4.2, Cor 4.4 | 98115b8e2580 formalized | 2 of 2 closed | proved |
| 1187–1189 | EJZ, BHV | a71f65809e0b formalized | 5 of 5 closed | proved |
| 1192–1195 | Abrams–Aranda, Ara, Preusser Thm 3 | 2bf4b5aca1b4 formalized | `binaryLeavitt_isPurelyInfiniteSimpleRing`, `binaryLeavitt_isExchangeRing`, `BinaryExampleSentences.manuscriptSentence_purelyInfiniteExchangePreusserSandwich` (binders only N, hN) | proved |
| 1206–1207 | Aranda Pino–Crow Cor 4.3 | d38df1795c78 formalized | `BinaryLeavitt.center_eq_bot` (every field) | proved |
| 1223–1224 | AGP Def 1.2 | c0fe92a1903d definition | `IsInfiniteIdempotent`, `IsPurelyInfiniteSimpleRing` | definition |
| 1225 | Abrams–Aranda | 4fb6ccd3e134 formalized | `AryLeavitt.isPurelyInfiniteSimpleRing (hd : 2 ≤ d)`, every field | proved |
| 1244–1246 | AGP Cor 1.7 | 5c5eeda68a8a formalized | `manuscriptSentence_matrixRingAgainPurelyInfinite` (printed hypotheses only) | proved |
| 1247–1248 | AGP Thm 2.4 | 6c03d472e975 formalized | `MFQuotientUnitsKOne.agpUnitKappa` (closed) | proved |
| 1249–1250 | BK | 55adb8bf7a88 formalized | `CountableAbelianMFPrintedRoute.manuscriptSentence_countableAbelianIsMFPrintedRoute` (closed) | proved |
| 1256–1257 | AGP Prop 1.5 | df9b558e0cb8 formalized | closed | proved |
| 1269–1272 | AGP Thm 2.4 (proof), Prop 1.5, Cor 1.7; Menal–Moncasi | afe1782dc7bc attribution | `MFQuotientUnitsKOne.manuscriptAGPInputs : AGPMatrixReduction ∧ AGPUnitKappa ∧ AGPUnitKappaResidue ∧ AGPUnitK1 ∧ AGPMenalMoncasiReduction ∧ AGPStepOne` (closed) | every quoted fact proved |
| 1327–1329 | Khanh–Thanh Thm 7.2 (proof) | 4321530b3fec formalized | `KhanhThanhDiagonal.printedKhanhThanhDecomposition_everyArity`, `scalarSurjective_everyArity` (closed) | proved |

## Attribution and credit only (no proof consumes them)

| tex | cite | row |
|---|---|---|
| 153–154 | OAI Ch. 3 | 374637bc6ac7 |
| 225–226 | Leavitt | 4bf35a8f555d (definition of the algebra, closed carrier) |
| 310–312 | BK94 | 27d456b915c0 |
| 313–315 | BK (NF iff nuclear and MF) | 14ee41b7f3cc |
| 315–318 | BK question, TWW | 82cac0c03a39 |
| 319–321 | Goldbring–Hart §6 | ba77c51e9726 |
| 325–327 | CDE, Korchagin, BDL | c8241b12c037 |
| 336–339 | OAI Prop 2.3 | 213a6657c8ff |
| 339–342 | Kun, Kun–Thom | de554b7cd342 |
| 349–351 | OAI, FFF | b89e90ea6607 |
| 351–353 | BDL Prop 1.5 | 9e2046c330c8 |
| 354–356 | Eckhardt | a494a9e94d28 |

## Still assumed

- **Hull's small cancellation theorem** (tex 303–305, `\cite{Hull}`; FFF §2 names the construction), row
  27e0c2f96db3 (attribution). The thm:torsion-free statement rows in tex 295–306, including the torsion-free clause
  of the abstract, are `partial`. They rest on
  `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (hgreendlinger), which carries Osin's
  appendix. The other walls on that route (hbridge, hKO, hW) are closed.
  - Residual: the eight post-(A) waist binders, owned by the other swarm's W1 lanes, plus w1-binder-1..8.
  - The quarantine scan of carrier modules found only `TheoremC.LiteratureInputs`, on this same row.
- No other cited result in tex 1–1337 is assumed anywhere in a formalized row's chain.

## Lean

- `GroupApproximation/Manuscript/NonMFSentences/CitationSweepIntroAudit.lean` (new): `#audit_closed_axioms` for
  `manuscriptShiftKernelIsOperatorMF`, `manuscriptMFNotClosedUnderIntSemidirect` and
  `printedNegativeConnesEmbeddingSentence`. Probe pending; it lands only after a green verdict.
