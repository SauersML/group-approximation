# cite-cstar: operator-algebra citation cluster

Lane cite-cstar (clone cs-limit, shared with dgo-analytic).  Scope: every sentence of
`non_mf_groups_exist.tex` citing BK, BK94, AkemannWalter, Eckhardt, CDE, OAI, Brown, STW, TWW,
GaoEtAl, Schafhauser, GoldbringHart or MIPRE.  Tex lines are origin/main lines at the time of
the sweep (09-12 ~10:15); keys are `metadata/NON_MF_SENTENCE_CENSUS.tsv` keys.

## Verdict

Every sentence of the cluster whose content a proof in the paper relies on is CLOSED by a
root-reachable declaration with a closed-axiom audit and no literature input.  The rest are
historical or credit sentences (ATTRIBUTION-ONLY).  One grade looks too strong (L316-320,
MIPRE), and one census decl list should name the size-free equivalence (L115-116).

## Proof-relevant sentences

| tex | key | cite | used by | carrier (all root-reachable) | state |
|---|---|---|---|---|---|
| 451-454 | 86ee71463acf | AkemannWalter | lem:kazhdan-projection-order, thm:transport, prop:max-infinite | `Manuscript.NonMFSentences.manuscriptSentence_kazhdanProjection : PrintedKazhdanProjection` (central star projection e_L in C*_max(L); image under the map induced by every unitary representation, every universe, fixes exactly the invariant vectors), `kazhdanProjection_central` | CLOSED (graded definition) |
| 506-509 | 87f873612529 | AkemannWalter | thm:transport proof | `OneSidedMFRadical.TransportProjectionCommutation.exists_projectionData` (binds `KD : KazhdanData L`, an ordinary intermediate hypothesis produced by `exists_kazhdanData`) | CLOSED |
| 740-742 | 0546c4f445c0 | AkemannWalter | prop:max-infinite proof | `MaximalCStarKazhdanProjection.KazhdanData.projection`, `StrictKazhdanCompression.proj/shift` | CLOSED (graded definition) |
| 760-762 | e4fcef4295ca | BK | prop:max-infinite proof | `ResiduallyFiniteDimensionalMF.isMFAlgebra` (separable RFD => MF), `MatrixCoronaFinite.mfAlgebra_isStablyFinite` | CLOSED |
| 1234-1237 | 55adb8bf7a88 | BK | thm:mf-quotient-units proof | `CountableAbelianMFPrintedRoute.manuscriptSentence_countableAbelianIsMFPrintedRoute` and its four steps | CLOSED |
| 115-116 | ad33e493e32f | BK | the MF-algebra definition every C*-statement uses | `OneSidedMFRadical.manuscriptIntroductionSeparableCStarAlgebraIsMFDef` | CLOSED, see note 1 |
| 87-98 | 88e8012cb87e | CDE | the MF-group definition | `OneSidedMFRadical.manuscriptIntroductionMFDefinition` | CLOSED |
| 102-105 | 837b7cffa562 | GaoEtAl, Schafhauser | headline transfer to the strong convention | `not_isStronglyOperatorMF_of_not_isOperatorMF` (the printed contrapositive; its only binder is the sentence's own premise, not MF), via `IsStronglyOperatorMF.isOperatorMF` | CLOSED, see note 4 |
| 262-270 | a96c09324a87 | Brown, STW, TWW | "here C*_max(W) is not nuclear" | `OneSidedMFRadical.manuscriptSentence_maximalCStarWNotNuclear` (Lance at the maximal algebra); the Brown/STW question and the TWW theorem are credit clauses | CLOSED + ATTRIBUTION |

Producer check for the Kazhdan projection (the one place a literature package could hide):
`exists_kazhdanData (hT : HasKazhdanPropertyT L)` is proved from
`KazhdanFiniteGeneration.exists_symmetric_generating_finset`,
`KazhdanGenerators.exists_pair_on_generators` and `HasKazhdanPropertyT.liftUniverse`, all theorems
on main; `HasKazhdanPropertyT` is the plain existence of a Kazhdan pair.  The endpoint module
closes with `#audit_closed_axioms manuscriptSentence_kazhdanProjection`.

## Attribution-only sentences (no proof relies on them)

| tex | key | cite | content |
|---|---|---|---|
| 153-154 | 374637bc6ac7 | OAI Ch. 3 | OpenAI built the first nonsofic group from H |
| 298-299 | 27d456b915c0 | BK94 | BK introduced MF/NF |
| 301-303 | 14ee41b7f3cc | BK | NF iff nuclear and MF (reported result) |
| 303-306 | 82cac0c03a39 | BK, TWW | the BK question and the TWW answer |
| 307-309 | ba77c51e9726 | GoldbringHart §6 | the MF problem |
| 313-315 | c8241b12c037 | CDE (+Korchagin, BDL: cite-korchagin) | CDE introduced MF groups |
| 324-327 | 213a6657c8ff | OAI Prop. 2.3 | credits the configuration |
| 337-339 | b89e90ea6607 | OAI (+FFF) | credits the group H |
| 342-344 | a494a9e94d28 | Eckhardt | Eckhardt's note |
| 1327-1329 | 2acc03ce92d4 | Brown | Brown's question |
| 1740-1741 | 5b0dfc92ce36 | OAI | provenance |
| 1781-1788 | c194394e4605 | Eckhardt | acknowledgments |

## Notes for census

1. L115-116 (ad33e493e32f).  `manuscriptIntroductionSeparableCStarAlgebraIsMFDef` is `Iff.rfl` onto
   `HasMFEmbedding`, which also asks for strictly increasing matrix sizes; the printed corona
   `Q_d` has arbitrary positive sizes.  The literal arbitrary-size statement is already on main
   and root-reachable: `OneSidedMFRadical.manuscriptArbitraryPositiveDimensionAlgebraMFDefinition`
   (CurrentManuscriptDefinitionRepairs.lean, via `MFAlgebraDimension.isMFAlgebra_iff`).  The row's
   decl list only names the first declaration; rows/cite-cstar.tsv adds the second.  No new Lean.
2. L316-320 (abfcbcb3af2b, MIPRE + GoldbringHart Prop. 6.1 / Rem. 6.2) is graded `formalized` with
   `NonMF.PriorWork.printedNegativeConnesEmbeddingSentence`.  That declaration proves the conclusion
   (a separable stably finite non-MF C*-algebra exists) through the paper's own reduced group
   algebra, not along the printed route from the failure of Connes embedding.  Under rule 9 a different
   route is `partial`; the sentence is a related-work report that no proof uses, so `attribution` with
   the conclusion decl kept as supplementary is the honest grade.
3. `MatrixCoronaFinite.MFAlgebraIsStablyFinite` binds `[PartialOrder A] [StarOrderedRing A]`; the
   Prop quantifies over every compatible order, so instantiating the spectral order gives the
   order-free printed sentence.  No action needed.
4. L102-105 (837b7cffa562).  Besides the injective corona representation, `IsStronglyOperatorMF` asks
   that the models reproduce the left regular norms, as printed.  The conditional baseline
   (`NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` l.78, l.97) accepts two findings here: carrier-data
   `IsStronglyOperatorMF` and open-predicate `IsStronglyOperatorMF.isOperatorMF`.  Both only say that
   nothing produces a strong datum.  The manuscript never claims one exists: the sentence asserts only
   the contrapositive, and that is proved outright.  Those baseline lines belong to baseline-debt;
   the grade needs no change.

## Owned elsewhere (not this lane)

Korchagin / BDL cites in L99-102, L273-276, L315: cite-korchagin.  LubotzkyOppenheim, Thom (L311-313)
and Kun16, KT19 (L328): cite-kazhdan.  ElekSzabo (L262): cite-sofic.  FFF (L292, L338): fff lanes.

## State

No new Lean needed for the cluster.  Scope finished; asking the lead for more.
