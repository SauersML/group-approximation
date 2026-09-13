# Lane ms-compress-4

## Item 2 (from 17:3x): W1 binder 1, the forest Prop under `OsinLemma94ClassCountInput`

CLAIM SameFaceDartForestStatement (statement and proof) GroupApproximation/GGT/VanKampen/CombMapSameFaceForest.lean

- Split agreed with w1-binder-1 in one direct message (~17:40). w1-binder-1 keeps the cutting-side count
  (`OsinLemma94CuttingSides`). This lane owns the forest Prop.
- The module carries w1-binder-1's spelling from its 17:3x draft: `CombMap.sameFaceDarts`, `CombMap.sameFaceVertices`,
  `CombMap.mem_sameFaceDarts`, `SameFaceDartForestStatement`, then `sameFaceDartForest`. Once it lands, w1-binder-1 drops those
  four declarations from its draft and imports this module.
- Not this lane: the non-cutting class half. It is owned by sec5-sentences (`OsinLemma94LongTransitionInput`),
  hull-count94 (`OsinLemma94ClassJoins`) and hull-component (bubble accounting).
- Model test by hand:
  - `IsPlanar := IsConnected ∧ χ = 2` (CombMap.lean:276), so a torus component plus a sphere component (χ = 0 + 2), where
    same-face edges can form a cycle, is excluded.
  - One edge: 2 darts, 2 vertices, `2 + 2 ≤ 4`, equality.
  - A loop has different faces on its two sides.
  - The empty case is excluded by `Nonempty`.
- Route:
  - Leaf induction over alpha-closed `T ⊆ sameFaceDarts f`.
  - A leaf exists. Otherwise a non-backtracking `next` gives a first vertex repeat, hence an `IsSimpleClosedWalk` inside `T`.
  - `IsSimpleClosedWalk.not_faceClass_alpha` and `SimpleClosedWalkSides.eqvGen_faceClass_of_sameCycle` then contradict
    `faceOf d = faceOf (alpha d)`.

# Range tex 658–739 (thm:normal-kazhdan, thm:compression-criterion)

Lead: session nonsofic-existence-49 (wave 2). Manuscript at origin/main 313212d8a (2507 lines). The sentence census on main
(`metadata/NON_MF_SENTENCE_CENSUS.tsv`, manuscript hash e66db325…) keys these rows at pre-chain-core line numbers
647–717; rows were matched by text.

CLAIM thm:normal-kazhdan hypothesis at printed generality (V_n(1)=1) GroupApproximation/Manuscript/NonMFSentences/NormalKazhdanPrintedHypothesis.lean

## Ledger

| tex | key | sentence (abbrev.) | status | carrier(s) | verdict |
|---|---|---|---|---|---|
| 659 | efed62e83cca | Let G be countable and let K ⊴ G have (T). | formalized | `manuscriptNormalKazhdanRadical`, `manuscriptNormalKazhdanPrintedRadical` | OK (setup of the statement) |
| 660–662 | 7778d54e679f | If every op-norm asymptotic rep satisfies ‖V_n(k)−1‖₂→0 … every corona hom is trivial on K. | formalized | `NonMFSentences.manuscriptPrintedNormalKazhdanNormalizedHypothesis` (796b5b00f), over `manuscriptPrintedNormalKazhdan` | FIXED (F5) |
| 668–669 | 99a3c8b3d8f9 | Suppose that a corona hom Θ is nontrivial on K. | structural | route endpoints | OK |
| 670–672 | a7997fb95c84 | Let e_K … and p its image … induced by Θ|_K. | formalized | `NormalKazhdanPrintedRoute.manuscriptSentence_kazhdanProjectionImage` | OK |
| 673–674 | 9658ec21017b | In any faithful rep of the corona, p is the projection onto the K-fixed vectors. | formalized | `manuscriptSentence171_maximalProjectionImageIsFixedProjection` (+ all universes), `KazhdanData.projection`, `exists_kazhdanData`, `CorrectedCornerProvenanceData` | OK; `exists_kazhdanData` is proved in-repo, and `CorrectedCornerProvenanceData` is data built by `exists_correctedCornerProvenanceData`, not a literature binder |
| 674–677 | 5abc59e0d8cc | Since gKg⁻¹=K, the range of Θ(g)pΘ(g)^* is Fix Θ(K), so | formalized | `nk_07_conjugate_proj`, `nk_07_commute_proj`, `manuscriptSentence_conjugatedProjectionRangesAgree` | OK |
| 678–680 | display 383951735318 | Θ(g)pΘ(g)^*=p | carrier | `nk_07_conjugate_proj` | OK |
| 681 | 3e281c6ee4c3 | and q=1−p is nonzero because Θ is nontrivial on K. | formalized | `nk_06_q_ne_zero`, `nk_06_rep_eq_one_of_q_eq_zero`, `manuscriptSentence171_…` | OK |
| 681–685 | 2e9741292f4c | By lem:central-corona-corner there is W_n … coordinate restriction of g ↦ qΘ(g). | formalized | `manuscriptCornerCoronaClass` | OK |
| 685–687 | 0239ca7d2b5e | Let π … induced by Θ̂|_K. | definition | `NonMFSentences.cornerCoronaUnitaryHom` | OK |
| 687–690 | 0c1ad4392d72 | Since q commutes with Θ(K) … π(e_K) is the coordinate restriction of qp=0. | formalized | `manuscriptSentence_inducedCornerKazhdanProjectionZero` | OK |
| 692–693 | 5c6689ae5e75 | Fix a free ultrafilter ω and let τ be the limit of normalized traces. | formalized | `manuscriptSentence_ultrafilterTraceIsTracialStateOnCorona`, `ultrafilterNormalizedTraceCLM`, `…WellDefinedTracialState` | OK |
| 694–696 | 00691a0fd65c | A norm-null sequence has vanishing traces … τ is a well defined tracial state. | formalized | `…ultrafilterTraceIsTracialStateOnCorona`, `norm_ultrafilterNormalizedTraceAdd_le`, `…WellDefinedTracialState` | OK |
| 696–697 | 54db830af92e | The hypothesis applies to (W_n) itself, so | formalized | `NormalKazhdanPrintedRoute.manuscriptSentence_traceOfCombinationTendsTo` | OK; conjunct 1 is tr(W_n(k))→1, and conjunct 2 is a leftover of the old limsup-combination proof (harmless extra) |
| 698–701 | display f3a27465fade | \|tr(W_n(k))−1\| ≤ ‖W_n(k)−I‖₂ → 0 | unassigned (stale display census) | proposed: `OneSidedMFRadical.norm_normTrace_sub_one_le` + conjunct 1 of `manuscriptSentence_traceOfCombinationTendsTo` | row added by this lane |
| 702–704 | 4e13d6e99e2d | in the normalized HS norm …, and therefore τ(π(u_k))=1 … | formalized | `manuscriptSentence_ultrafilterTraceOfInducedGeneratorIsOne`, `…TraceOfCornerUnitaryIsOne`, `cornerCoronaUnitaryHom` | OK |
| 704–706 | 377d3a03266b | The trivial character χ … χ(u_k)=1 … χ(e_K)=1. | formalized | `manuscriptSentence_trivialCharacterIsStateWithValues` | OK |
| 706–708 | 82dded1b13b3 | The two states agree on u_k, on ℂ[K], on C*_max(K). | formalized | `manuscriptSentence_statesAgreeOnGeneratorsSpanAndAlgebra` | OK |
| 708 | fb1df1a24e3f | So | formalized | `manuscriptSentence_oneEqualsZeroContradiction` | OK (display fragment) |
| 709–711 | display (not in the display census) | 1=χ(e_K)=τ(π(e_K))=τ(0)=0 | none | `NonMFSentences.manuscriptSentence_oneEqualsZeroContradiction` | row added by this lane |
| 712 | 7409ff7e2c5f | a contradiction. | formalized | `manuscriptSentence_oneEqualsZeroContradiction`, `manuscriptNormalKazhdanRadical_ultrafilterRoute` | OK |
| 717 | 4bc46d4603fd | Let G be countable and let L ≤ G have (T). | formalized | `manuscriptCompleteOneSidedCompressionCriterion`, `manuscriptOneSidedCompressionCriterion` | OK |
| 718–720 | 2f041595e7a7 | If K ⊴ G has (T) and K ≤ 𝔇_G(L), every hom to an MF group is trivial on K. | formalized | `manuscriptOneSidedCompressionCriterion`, `manuscriptSentence42_…`, `PrintedCompressionCriterion`, `manuscriptPrintedCompressionCriterion` | OK |
| 720–723 | 50ca303a15db | In particular, nontrivial K ⇒ G not MF; G (T) and 𝔇_G(L)=G ⇒ every MF hom trivial. | formalized | `manuscriptSentence43_…`, `manuscriptSentence44_…`, `manuscriptFullRadicalKillsMFTargets` | OK |
| 729–731 | 47c65457b63c | By cor:defect-hs, every op-norm asymptotic rep satisfies ‖V_n(k)−1‖₂→0 for k ∈ K ≤ 𝔇_G(L). | formalized | `manuscriptCompressionDefectHSInvisible`, `manuscriptPrintedDefectShadowInclusion`, `PrintedCompressionCriterionHSHypothesis` | OK (conclusion over all `OpAlmostRepresentation`, which is stronger than printed) |
| 731–734 | 4cd99c2ee1cb | By thm:normal-kazhdan every corona hom is trivial on K, and by prop:mf-residual-calculus so is every MF hom. | formalized | `normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect`, `manuscriptPrintedDefectNormalKazhdanRadical`, `PrintedCompressionCriterionCoronaTrivial` | OK |
| 734–735 | 570d0f5d862a | If K ≠ 1, G does not embed in an MF group, so G is not MF. | formalized | `manuscriptSentence43_…`, `manuscriptOneSidedCompressionCriterion` | OK |
| 735 | 91a29e789438 | The last assertion is the case K=G=𝔇_G(L). | formalized | `manuscriptSentence44_full_defect_gives_full_radical` | OK |

No `\cite` occurs in tex 658–737.

## Checks

- **Root reachability.** GroupApproximation.lean imports PrintedCriterion, PrintedForms, CompressionCriterion, NormalKazhdan,
  NormalKazhdanPrintedRoute, HSVanishesProducers, CanonicalSector, NonMFSentences/NormalKazhdanUltrafilterRoute,
  NonMF/Audit/Sec2, NonMF/Audit/Intro, OneSidedMFRadical/Audit and Endpoint/OneSidedTransportAudit.
  CorrectedCornerProjectionZero and SentenceNormalizedAlmostRepresentationClosure are reached through those.
- **Axiom audits.** `#audit_closed_axioms` covers manuscriptPrintedNormalKazhdan (Sec2:372), …_ultrafilterRoute (its module
  and Sec2:446), manuscriptPrintedCompressionCriterion (Sec2:452), manuscriptOneSidedCompressionCriterion (Intro:72,
  OneSidedTransportAudit:175), manuscriptCompleteOneSidedCompressionCriterion (Sec2:456) and
  manuscriptFullRadicalKillsMFTargets (Sec2:462, PrintedAudit:19). The sentence lemmas carry `#audit_axioms`.
- **Conditional baseline.** No carrier of this range has a live line. The only mention is one REMOVED line (open-predicate
  manuscriptPrintedNormalKazhdan, stale at 63f147d7b).
- **Definitions.**
  - `OpAlmostRepresentation`: unitary models, asymptotic multiplicativity in the L2 operator norm.
  - `HSVanishes`: √hsLengthSq = ‖V_n(k)−1‖₂, normalized by the card.
  - `ManuscriptCoronaMFInvisible`: trivial under every hom into U(∏M_{d_n}/⊕M_{d_n}).
  - `KillsMFTargetsOn`: homs into countable `IsCDEOperatorMF` groups; MF is printed for countable groups (tex 87).
  - `printedDefect`: normal closure of [ucu⁻¹, ℓ].
  - Commutator convention [g,h]=ghg⁻¹h⁻¹ (tex 156) = Mathlib `⁅g,h⁆`.

## Findings

- **F5 (printed generality gap, fixing).** tex 410–411 defines an operator norm asymptotic representation WITH V_n(1)=1.
  `PrintedNormalKazhdan` quantifies its hypothesis over every `OpAlmostRepresentation`, without V_n(1)=1, so the Lean
  hypothesis assumes more and the Lean theorem is weaker than printed.
  - Fix: `NonMFSentences.PrintedNormalKazhdanNormalizedHypothesis` quantifies over `PrintedOpAlmostRepresentation`
    (`SentenceNormalizedAlmostRepresentationClosure`).
  - Proof: `normalizedHSHypothesis_iff` (normalization via `opAlmostRepresentationToPrinted`; at the identity
    ‖A_n(1)−1‖₂ ≤ ‖A_n(1)−1‖ → 0 by `map_one_vanishing`), then `manuscriptPrintedNormalKazhdan`.
  - Status: CLOSED. LANDED 796b5b00f (probe 0913-170955-91871 GREEN, BUILT, `#audit_closed_axioms` in the module); queued for
    wiring. Row 7778d54e679f is re-graded onto it in `metadata/nm-census-rows/ms-compress-4.tsv`.
- **F2 (tex badge, sent to main).** tex 664 badges `NormalKazhdanPrintedRoute.manuscriptNormalKazhdanRadical_printedRoute`, the
  old limsup-combination proof. The printed proof is the ultrafilter-trace route
  `NonMFSentences.manuscriptNormalKazhdanRadical_ultrafilterRoute`.
- **F1 (stale display census).** `metadata/NON_MF_DISPLAY_CENSUS.tsv` (hash b686680…) lists four `unassigned` displays of the old
  proof (ba198b2b9795, 099d5bf78229, c3da18932be7, 63be4079d36b: a=Σα_k u_k, ‖a−e_K‖<1/4, …). They are not in the current tex,
  which has no `alpha_k u_k` and no `tfrac14`. The census lane should drop them on regeneration. The current displays at
  698–701 and 709–711 get rows from this lane.
