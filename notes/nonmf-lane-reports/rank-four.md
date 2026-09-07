# Lane `rank-four`: `thm:headline` at `H = EL_4(L_{F_2}(1,2))`

Task: re-create at rank four everything the rank-twelve modules prove for
`EL_12`, as new modules, without touching the rank-twelve ones.

## Landed

| commit | modules | jobs |
|---|---|---|
| `bd0e81062f43b5189f5433777249ad70bdc80d76` | `RankFourEndpoints.lean`, `RankFourSimplicity.lean` | 4383 / 4450 |
| `7908cd9bcd9ea4ed1f1fce22955948536334a472` | `RankFourConfiguration.lean`, `RankFourEJZInstance.lean` | 4389 |
| `81202607aa74ff1ea93b5801ade49bf98a454ac0` | `HeadlineTheoremRankFour.lean`, `ReducedCStarConsequenceRankFour.lean`, `RankFourAudit.lean` | 4464 / 4470 |
| `acea48a28f00f7edda9877000c114d1adb600d5a` | `RankFourOneSidedBridge.lean` | 4388 |

All under `GroupApproximation/Manuscript/OneSidedMFRadical/`, namespace
`GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoint` (the
headline and C⋆ modules live one namespace up, as at rank twelve).  The root
import list is the lead's to wire.

## The printed endpoints and their carriers

| printed | carrier |
|---|---|
| `thm:headline`, whole | `manuscriptPrintedHeadlineRankFour` |
| `thm:headline`, group clauses | `manuscriptBinaryLeavittHeadlineRankFour` |
| `thm:headline`, radical package | `manuscriptBinaryLeavittFullRadicalRankFour` |
| `thm:headline`, reduced-C⋆ clause | `manuscriptReducedCStarConsequenceRankFour` |
| `thm:headline`, maximal-C⋆ clause | `manuscriptMaximalCStarNotFiniteRankFour` |
| Blackadar–Kirchberg refutation form | `manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour` |
| `prop:simple` | `RankFourEndpoint.manuscriptPropositionSimple` |
| compression step of `thm:full-defect-ring` at `R` | `RankFourEndpoint.manuscriptPropositionDefect` |
| `Rad_MF(H) = H` | `RankFourEndpoint.rankFour_actualCoronaMFResidual_eq_top` |
| "Both groups have property (T)" (EJZ) | `RankFourEndpoint.printedBothGroupsHaveKazhdanPropertyT` |
| strictness `uLu⁻¹ ⊊ L` | `RankFourEndpoint.u_conj_corner_lt` |

## What is rank-four-specific

The printed mark is `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)`.  At rank four it
cannot be an elementary root: every index pair meets the corner `{1,2,3}`.  So
`RankFourEndpoint.c` is a commutator, its matrix value is a calculation
(`c_val`), and its centrality relative to the corner is a calculation rather
than the disjoint-support argument used at rank twelve.  Accordingly
`PrintedDefectConfiguration` has four conjuncts here, not three: property (T)
for the corner, centrality of `c`, the compression `uLu⁻¹ ≤ L`, and the
commutator `[ucu⁻¹, ℓ] = d`.

Nothing else is rank-specific.  The compressor `u = u₃u₂u₁` and the conjugation
identity are already in `Leavitt/RankFourCompressors.lean`; normal generation of
the defect, root detection, simplicity, the compression criterion, and the two
C⋆ clauses all ask only for three indices or for nothing at all.

## Deviations from the brief

1. `corner_hasKazhdanPropertyT` and the corner-embedding machinery live in
   `RankFourEndpoints`, not `RankFourConfiguration`, so that
   `RankFourEJZInstance` can state its agreement lemma without waiting for the
   configuration.
2. The configuration was built directly on `Leavitt/RankFourCompressors.lean`
   rather than on lane `ring-b-alg`'s `OneSidedCompressor.lean`, which had not
   landed at the time.  It has since landed, and `RankFourOneSidedBridge.lean`
   reconciles the two: `corner = OneSidedCompressor.core R`,
   `u = OneSidedCompressor.compressor (ofLeavittFamily leavittFamily)`,
   `c = centralMark …`, `ell = printedEll R`, `defect = printedDefectRoot …`.
   All five are definitional except the two involving the complementary
   idempotent, which the two developments spell `s₁t₁` and `1 - s₀t₀`.  So
   there is one rank-four corner under two names, not two corners, and
   `printedDefect_core_eq_top` states the saturation in
   `OneSidedCompressor`'s own vocabulary.
3. The maximal-C⋆ clause is *inside* `PrintedHeadlineRankFour`.  At rank twelve
   it was proved (in `PrintedLeavittEquations`) but left out of the headline
   package, which the manifest wrongly called complete.

## Traps worth reusing

* `Subgroup.closure_induction` over the *subgroup-subtype* group structure
  times out in `whnf` at 200000 heartbeats here, and does so even when the
  statement is generic in the coefficient ring, because every step needs a
  `change` across `⟨x, hx⟩ * ⟨y, hy⟩`.  Going through
  `elementaryRootSet_generate` plus `Subgroup.closure_le` avoids the issue
  entirely and is shorter.
* `HilbertHotel.normalClosure_elementaryRoot_eq_top` needs rank `≥ 5` and is
  unusable at rank four.  `normalClosure_elementaryRoot_p1_eq_top` and
  `elementaryGroup_normal_eq_top_of_elementaryRoot_mem` need only three
  indices and hold over every ring with a binary Leavitt family.
* `mul_assoc` in a `simp` set right-associates every product, so a relation
  like `t₀ * e = 0` never appears as a subterm of a longer word.  The
  absorbing form `∀ x, t₀ * (e * x) = 0` has to be supplied alongside it, and
  the `unusedSimpArgs` linter (an error under `-DwarningAsError=true`) is what
  tells you which of the two actually fired.

## Open

Nothing in the brief is open, and the lead's follow-up bridging lemma
(`compressor_eq_oneSidedCompressor`) is landed.  The one thing outside it: the `\leanverified`
lines of `thm:headline` in `non_mf_groups_exist.tex` still name the
rank-twelve declarations, and the manifest and census rows still point there.
Those are the lead's and the tex peer's to repoint at the names in the table
above.

## Sentence-to-lemma table for the printed proof of Theorem B (2026-09-07)

`non_mf_groups_exist.tex` lines 989-1106, the proof environment of
`thm:full-defect-ring`.  Forty-two printed sentences; carriers landed in
`GroupApproximation/Manuscript/OneSidedMFRadical/FullDefectRingSentences.lean`
(commit `7d876ae10`), sub-namespace `FullDefectRingSentences`, one
`manuscriptSentence_*` per sentence, each with `#audit_axioms`.

Status column: **U** unconditional, **P** partial (what is missing is named),
**D** definitional or structural, no lemma of its own.

### Part one, the group `B`

| # | Printed sentence | Carrier | Lemma it spends | |
|---|---|---|---|---|
| 1 | In `𝒞` put `s=s₀`, `t=t₀`, `e=1-st`. | `manuscriptSentence_ringData` | `OneSidedInverse.e_eq`; the assignment itself is the definition `UniversalPair.pairInverse` | D |
| 2 | Then `ts=1`, `e²=e`, `es=te=0`, and `t₁es₁=1`. | `manuscriptSentence_ringRelations` | `OneSidedInverse.t_mul_s`, `e_mul_e`, `e_mul_s`, `t_mul_e`; `UniversalPair.printedFullnessWitness` | U |
| 3 | Put `G=B=EL₄(𝒞)` and `L=EL₃(𝒞)` on coordinates 1,2,3. | `manuscriptSentence_groupsGandL` | `OneSidedCompressor.coreEmbedding_range`; `G=B` is `UniversalGroupB.B` | D |
| 4 | `𝒞` is f.g., so both groups have (T) by EJZ 1.1, and `B` is f.g. by BHV 1.3.1. | `manuscriptSentence_finitelyGeneratedPropertyT` | `UniversalPair.isFinitelyGeneratedRing`, `UniversalGroupB.hasKazhdanPropertyT`, `corner_hasKazhdanPropertyT`, `UniversalGroupSigma.finitelyGenerated` | U |
| 5 | For `i=1,2,3` set `uᵢ = e₄ᵢ(t-1)e_{i4}(1)e₄ᵢ(s-1)e_{i4}(-t)`. | `manuscriptSentence_compressorPieceDef` | `OneSidedCompressor.compressorPiece` | D |
| 6 | Its block on `(i,4)` is `(s e; 0 t)`. | `manuscriptSentence_compressorPieceBlock` | `compressorPiece_val` | U |
| 7 | so `u=u₃u₂u₁ ∈ EL₄(𝒞)` is the displayed matrix. | `manuscriptSentence_compressorMatrix` | `compressor_val`, stated against the printed literal | U |
| 8 | invertible as a product of elementary matrices. | `manuscriptSentence_compressorInvertible` | `compressorMatrix_mul_inv`, `compressorInvMatrix_mul` | U |
| 9 | `u e_{ij}(a) = e_{ij}(sat) u` (`eq:intertwine`). | `manuscriptSentence_intertwine` | `compressor_mul_coreRoot` | U |
| 10 | both sides differ from `u` by one entry, since `sa·ts=sa` and `sa·te·t^{j-1}=0`. | `manuscriptSentence_intertwineEntries` | **new here**; no lemma states the two entry computations separately | U |
| 11 | So `uLu⁻¹ ≤ L`. | `manuscriptSentence_compressesCore` | `compressor_mem_compressionSet` / `compressor_compresses_core` | U |
| 12 | `c=[e₄₁(e),e₁₄(t)]=diag(1,1,1,1+et)`. | `manuscriptSentence_centralMark` | `centralMark_eq_commutator`, `centralMark_val` | U |
| 13 | computed using `te=0`; such a diagonal commutes with every `diag(A,1)`, so `c ∈ C_G(L)`. | `manuscriptSentence_centralMarkCentral` | `centralMark_commute_core` | U |
| 14 | Both `uc` and `e₁₂(e)u` equal `u+et E₁₄`; so `ucu⁻¹=e₁₂(e)`. | `manuscriptSentence_conjCentralMark` | `compressor_mul_centralMark`, `compressor_conj_centralMark` | U |
| 15 | For `ℓ=e₂₃(1)`, `d=[ucu⁻¹,ℓ]=e₁₃(e) ∈ 𝔇_G(L)`. | `manuscriptSentence_defect` | `defect_eq`, `printedDefectRoot_mem_printedDefect`, `printedEll` | U |
| 16 | Let `N` be the normal closure of `d` in `G`. | `manuscriptSentence_normalClosureOfDefect` | `Subgroup.subset_normalClosure`; the formal `N` is the bound variable of `FullIdempotent.elementaryGroup_normal_eq_top_of_full` | D |
| 17 | `[e₄₁(a),e₁₃(e)]=e₄₃(ae)`, `[e₄₃(ae),e₃₂(b)]=e₄₂(aeb)`. | `manuscriptSentence_steinbergPair` | `elementaryRoot_commutator`, at the two printed index triples | U |
| 18 | So `e₄₂(1)=e₄₂(t₁es₁) ∈ N`. | `manuscriptSentence_fullnessRootRewrite` | **new here**; `elementaryGroup_normal_eq_top_of_full` takes the general indexed sum and never singles out the one-term case | U |
| 19 | Signed permutation matrices conjugate this to every off-diagonal position. | `manuscriptSentence_signedPermutationsReachEveryPosition` | `FullIdempotent.elementaryGroup_normal_eq_top_of_full` | **P**: conclusion carried, route not. That lemma uses `exists_two_further_indices` and Steinberg conjugation; `ElementaryWeyl.weyl` exists but the full-defect proof does not spend it |
| 20 | `[e_{ij}(1),e_{jk}(r)]=e_{ik}(r) ∈ N`. | `manuscriptSentence_steinbergSpreadsCoefficients` | `elementaryRoot_commutator` | U |
| 21 | So `N=G`, and `𝔇_G(L)=G`. | `manuscriptSentence_defectIsEverything` | `FullIdempotent.printedDefect_eq_top` | U |
| 22 | By `thm:compression-criterion` with `K=G`, every hom from `G` to an MF group is trivial. | `manuscriptSentence_homFromBTrivial` | `UniversalGroupB.hom_eq_one` | U |
| 23 | `σ=e₁₂(1)e₂₁(-1)e₁₂(1)` has order four. | `manuscriptSentence_sigmaOrderFour` | `UniversalGroupSigma.orderOf_sigma` | U |
| 24 | `σe₁₃(-r)σ⁻¹=e₂₃(r)`, `[e₁₃(r),σ]=e₁₃(r)e₂₃(r)`, `[e₁₂(1),[e₁₃(r),σ]]=e₁₃(r)`. | `manuscriptSentence_sigmaConjugation` | `UniversalGroupSigma.elGen_mem_normalClosure` | **P**: the three identities are steps inside that proof and have no separate names; the carrier is its conclusion |
| 25 | with signed permutation matrices, `σ` normally generates `B`. | `manuscriptSentence_sigmaNormallyGenerates` | `UniversalGroupSigma.normalClosure_sigma_eq_top` | **P** in route only: conclusion exact, but the proof ends with `elementaryGroup_normal_eq_top_of_elGen_mem` |

### Part two, rank two

| # | Printed sentence | Carrier | Lemma it spends | |
|---|---|---|---|---|
| 26 | Let `R` satisfy the hypothesis; by `lem:two-copies` choose `wᵢvⱼ=δᵢⱼ`. | `manuscriptSentence_twoCopies` | `RankDescentPrinted.manuscriptTwoCopiesLemma`, `RankDescent.ofFull` | U |
| 27 | `sᵢ↦vᵢ`, `tᵢ↦wᵢ` is a unital ring hom from `𝒞` onto the subring `S ≤ R`. | `manuscriptSentence_universalProperty` | `UniversalPair.lift`, `lift_v`, `lift_w` | **P**: the corestriction to `S` is not carried; the formal map goes into `R` itself and `S` is never named. Every later step uses only the `Sᵢ,Tⱼ` built from the `vᵢ,wᵢ`, so the rest goes through at `R` |
| 28 | so `EL₄(S)` is a homomorphic image of `B`, and every hom from `EL₄(S)` to an MF group is trivial. | `manuscriptSentence_imageOfB` | `UniversalGroupB.toElementaryFour`, `toElementaryFour_root`; `FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsAllCharacteristics` | **P**: target is `EL₄(R)`, not `EL₄(S)`. Also needs `[Countable R]`, which the printed sentence does not say and which `PrintedFullComplementaryIdempotents` does require |
| 29 | Put `S₁=v₀v₀,…,T₄=w₁w₁`, so `TᵢSⱼ=δᵢⱼ`. | `manuscriptSentence_lengthTwoWords` | `RankDescent.wordS`, `wordT`, `wordT_mul_wordS` | U |
| 30 | put `p=∑ᵢSᵢTᵢ`. | `manuscriptSentence_pIdem` | `RankDescent.pIdem` | D |
| 31 | `ȷ(A)=1-p+∑_{ij}SᵢA_{ij}Tⱼ`. | `manuscriptSentence_jMapDef` | `RankDescent.jMap`, `jBody` | D |
| 32 | Since `(1-p)Sᵢ=0`, `Tⱼ(1-p)=0`: `ȷ(AB)=ȷ(A)ȷ(B)`, `ȷ(I)=1`. | `manuscriptSentence_jMapMultiplicative` | `one_sub_pIdem_mul_wordS`, `wordT_mul_one_sub_pIdem`, `jMap_mul`, `jMap_one` | U |
| 33 | so `Ψ(A)=diag(ȷ(A),1)` is a hom `GL₄(S)→GL₂(R)`. | `manuscriptSentence_psiIsDiag` | `RankDescent.blockDiagHom`, `psiUnits` | U |
| 34 | `Ψ(e_{ij}(r))=diag(1+SᵢrTⱼ,1)=[e₁₂(Sᵢr),e₂₁(Tⱼ)]`, since `TⱼSᵢ=0`. | `manuscriptSentence_psiOnRoots` | `psi_elementaryRoot`, `RankDescentPrinted.gen_eq_printed_commutator`, `gen_val` | U |
| 35 | So `Ψ(EL₄(S)) ≤ EL₂(R)`. | `manuscriptSentence_psiLandsInEL2` | `psiUnits_mem` | U |
| 36 | `ρ∘Ψ` trivial on `EL₄(S)`, so `ρ` kills `Ψ(e₁₂(1))=diag(1+S₁T₂,1)`. | `manuscriptSentence_rhoKillsGenerator` | `RankDescent.descent_elementaryRoot` | U |
| 37 | which normally generates `EL₂(R)` by `lem:rank-two` with `v=S₁,w=T₁,a=S₂,b=T₂`. | `manuscriptSentence_generatorNormallyGeneratesEL2` | `normalClosure_descent_root_eq_top`; closed form `RankDescentPrinted.manuscriptRankTwoNormalGeneration` | U |
| 38 | So `ρ` is trivial. | `manuscriptSentence_rhoTrivial` | `FullDefectRankTwo.hom_eq_one_of_rankFour` at `n=2` | U |
| 39 | the image of `B` in `EL₂(R)` contains `Ψ(e₁₂(1))`, so it normally generates. | `manuscriptSentence_imageOfBNormallyGeneratesEL2` | `UniversalGroupB.toRankTwo_root_one`, `normalClosure_toRankTwo_range` | U |

### Part three, all ranks

| # | Printed sentence | Carrier | Lemma it spends | |
|---|---|---|---|---|
| 40 | For `n≥3`, signed permutation matrices conjugate `e₁₂(r)` to `e_{ij}(±r)`, so the copy of `EL₂(R)` on 1,2 normally generates `EL_n(R)`. | `manuscriptSentence_copyOfEL2` | `FullDefectRankTwo.blockEmbed`, `blockEmbed_upperRoot` | **P**: conclusion carried inside `hom_eq_one_of_rankFour`; route not. Steinberg conjugation replaces the signed permutations, as in row 19 |
| 41 | A hom from `EL_n(R)` to an MF group is trivial on that copy, hence trivial. | `manuscriptSentence_homFromELnTrivial` | `FullDefectRankTwo.hom_eq_one_of_rankFour`, at every `n ≥ 2` | U |
| 42 | and the image of `B` in that copy normally generates `EL_n(R)`. | `manuscriptSentence_imageOfBNormallyGeneratesELn` | `UniversalGroupB.exists_hom_normallyGenerating` | U |

Counts: 34 unconditional, 5 partial (19, 24, 25, 27, 28, 40 -- six rows, of which
25 and 40 are partial in route only), 5 definitional.  Two carriers are new
content (10 and 18); everything else is a wrapper.

One thing worth the lead's eye beyond the table: row 28 needed `[Countable R]`.
`FullDefectRing.PrintedFullComplementaryIdempotents` quantifies over countable
rings, and the printed sentence at that point in the proof does not say so.
The countability is harmless where the theorem is applied (`𝒞` is countable,
and Theorem B's own hypothesis chain supplies it), but a reader following the
printed proof line by line will not find it stated.
