# cite-kazhdan

Lane cite-kazhdan (clone nm-d, shared with fff-quotient).  Citation cluster: property (T) and
Kazhdan -- BHV Theorem 1.3.1, BHV Example 1.7.4(i), Lubotzky--Oppenheim, Thom, Kun16.  Tex and
sentence map read at origin/main, 2026-09-12.

## Per sentence

- **6edef6dc2d68** (tex 311--313; LubotzkyOppenheim, Thom) -- CLOSED, orphan module.
  Carrier `GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_positiveMFProblemAnswerMakesEveryCountableGroupMF`
  `: PrintedPositiveMFProblemAnswerMakesEveryCountableGroupMF`, landed d6081c7c4.  The printed sentence is
  conditional ("would make").  The carrier proves that conditional: if every separable stably finite
  C*-algebra is MF, then every countable group is MF, via `reducedGroupCStar_separable_stablyFinite`
  and `isCDEOperatorMF_of_hasMFEmbedding_reducedGroupCStar`.  The attribution clause carries no proof
  obligation.  Evidence: compiled green in go-lemma42.green.0911-231324-58545 (md5 7229b32d... equals
  origin/main).  Open for the lead: `IntroSentences` is not reachable from the root.  It is queued in
  wire-queue.txt (09-09 orphans).

- **0939d33e1ff4** (tex 939--943; BHV Theorem 1.3.1 for EL_4(C)) -- CLOSED, rooted.
  The cited inference (property (T) implies finitely generated) is proved internally by
  `GroupApproximation.KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`.  It is packaged as
  `HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated` (7b66deac0) and used in
  `UniversalRingSentences.manuscriptSentence_universalRingPrintedReasons` (a686eaa56; map row: compiled
  probe 0911-210130-73901).  The EJZ clause of the same sentence belongs to cite-ejz.

- **a71f65809e0b** (tex 1172--1175; BHV Theorem 1.3.1 for H) -- CLOSED, rooted.
  `HeadlineCitationSentences.headlineGroup_finitelyGenerated_via_propertyT : Group.FG RankFourEndpoint.H`,
  from `fg_of_hasKazhdanPropertyT` and `RankFourEndpoint.hasKazhdanPropertyT_viaEJZ` (7b66deac0).

- **77028123cdd6** (tex 1598--1600; BHV Example 1.7.4(i)) -- IN PROGRESS (new carrier probing).
  Both clauses were already proved in rooted modules:
  - `ExplicitIntegralLinearModel.gammaBar_residuallyFinite` (316ed12b9) follows the printed route.  It
    uses the integral realization `gammaIntEquivGammaBar` and `generalLinearGroup_int_residuallyFinite`,
    which reduces modulo |z|+1 at a nonzero entry z of g-1.
  - `CommutingLampCollapse.gammaBar_hasKazhdanPropertyT` (27ee46d2a) has no premises.  It comes from
    `LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT` (P13 Hodge certificate, no
    native_decide).

  The printed reason had no statement of its own.  New module
  `GroupApproximation/Manuscript/NonMFSentences/GammaBarKazhdanSentences.lean` (landed unverified
  8986b82f5) proves `PrintedReductionModSuitableIntegerSeparates`: any two distinct integral matrices,
  of any shape, are separated modulo a nonzero integer.  It bundles the sentence as
  `PrintedGammaBarResiduallyFiniteAndKazhdan`.  Probe 0912-104738-60985 failed only on the deprecated
  `push_neg`; that is fixed and the module is re-probing.

  Census correction: the map row names only `gammaBar_residuallyFinite`, and its note is copied from
  c48c7da870a2 (the index-8 sentence).  The corrected row goes to metadata/nm-census-rows/cite-kazhdan.tsv
  after green.  Rows 3229365c29c6, c48c7da870a2 and 7f667d9f1cb7 take Gamma-bar to be
  `ExplicitLinearModel.gammaBar`, and this carrier does the same.

- **de554b7cd342** (tex 326--330; Kun16, KT19) -- OWNED BY cite-sofic (agreed 2026-09-12).

- **61827aea7807** (tex 187; intro trace sentence and footnote, thm:normal-kazhdan) -- OWNED BY
  hs-vanishes (census2 U5).

- **thm:normal-kazhdan** (tex 646--701): no sentence there cites BHV, Lubotzky--Oppenheim, Thom or
  Kun16.  Its 21 rows at origin/main are 19 formalized, 1 structural and 1 definition.

## Wiring needed (lead)

- `GroupApproximation.Manuscript.NonMFSentences.IntroSentences` (6edef6dc2d68): already queued.
- `GroupApproximation.Manuscript.NonMFSentences.GammaBarKazhdanSentences`: after its green probe.
