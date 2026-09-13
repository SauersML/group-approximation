# Lane ms-intro-2: tex 166–232 (eq:intrinsic-defect, eq:defect-functorial, eq:leavitt)

Lead: session nonsofic-existence-49 (wave 2). Line numbers are at origin/main 68481e4d7. Census rows are matched by
text against `metadata/NON_MF_SENTENCE_CENSUS.tsv`, whose line numbers are at the pre-chain-core hash.

CLAIM carriers for 9bab404c96c5, 6b5d4b5c3081, 29d7a8ccf93a, 270c3118af88 in module
`GroupApproximation/Manuscript/NonMFSentences/IntroCompressorSentences.lean` (path free on origin, disk and every lanes/*.files at 16:55).

## Ledger (15 rows)

| key | tex | status on main | verdict |
|---|---|---|---|
| 56d73653208a | 164–172 display eq:intrinsic-defect | definition: `printedDefect`, `printedDefectSet`, `manuscriptSentence40_printedDefect_display` | PASS: normal closure of `[ucu⁻¹, ℓ]` with `u ∈ compressionSet L`, `c` commuting with `L`, `ℓ ∈ L`, exactly as displayed |
| 50a97a1f5896 | 173 "For every homomorphism" | structural | PASS: lead-in; the display's content is carried by 51077cfd1fa7 |
| 51077cfd1fa7 | 174–180 eq:defect-functorial + "since …" | formalized: `manuscriptPrintedDefectFunctorial` | PASS: closed Prop for every homomorphism of groups in `Type`; the proof is the printed one clause for clause (`map_printedDefect_le`) |
| 270c3118af88 | 182–185 criterion summary | formalized: `manuscriptOneSidedCompressionCriterion` | GAP (form): the carrier's clause is `K ≤ manuscriptCoronaMFResidual G`; the sentence says K "dies in every MF image". Countability is inherited from thm:compression-criterion. Fix: closed Prop "every homomorphism from G to an MF group is trivial on K", assembled from the criterion and the residual calculus |
| 0b6c334de950 | 187 "The proof has two steps." | structural | PASS |
| a700a5798fd5 | 187–194 first step | formalized: 15 declarations | PASS (spot check): concrete statements in CompressionCriterionSentences and KazhdanTransportSentences; no literature binder in the signatures read |
| 2189c5b26e10 | 194–196 "Second, let K …" | structural | PASS: sets hypotheses only |
| e63d12558c72 | 196–199 corner compression | formalized: 3 declarations | PASS (spot check) |
| 61827aea7807 | 199–205 limiting trace + footnote | formalized: `manuscriptSentence_limitingTraceIsTrivialCharacter`, `manuscriptSentence_compressionOutlineFootnote`, `manuscriptNormalKazhdanRadical_ultrafilterRoute` | PASS: closed Props |
| 9bab404c96c5 | 207–208 stable letter of an ascending HNN extension | structural ("not used in any proof") | GAP (classification): the sentence asserts mathematics. Fix: closed Prop over Mathlib's `HNNExtension L ⊤ φ.range` for every group with property (T) and every proper injective endomorphism: `t ∈ compressionSet (of.range)` |
| 91310d39561c | 208–210 `e_ij(a)`, `EL_n(R)` | definition: `elementaryUnit`, `elementaryGroup`, `manuscriptSentence54_…` | PASS: `1 + single i j a`, closure of those units |
| 6b5d4b5c3081 | 211–215 pair `s,t` gives a compressor | formalized: `FullDefectRingSentences.manuscriptSentence_{compressorMatrix,intertwine,defectIsEverything}` | GAP (generality): all three carriers are stated over the universal ring 𝒞 only; the sentence is for every unital ring R with ts = 1. Fix: closed Prop over every ring, from the general `OneSidedCompressor` lemmas (`compressor_mem_compressionSet`, `compressor_mul_coreRoot`, `centralMark_commute_core`, `defect_eq`) and `FullIdempotent.elementaryGroup_normal_eq_top_of_full` |
| 29d7a8ccf93a | 215–219 universal ring 𝒞, EL₄(𝒞) maps with normally generating image | formalized: `manuscriptSentence_universalProperty`, `manuscriptSentence_imageOfBNormallyGeneratesELn`, `UniversalPair.UniversalPairRing` | GAP (closure): `imageOfBNormallyGeneratesELn` takes a section variable `Q : ProperlyInfiniteUnit R`, not the printed hypotheses. Fix: closed Prop for every countable ring with ts = 1 and 1 − st full and every n ≥ 2, through `RankDescent.ofFull` and `UniversalGroupB.exists_hom_normallyGenerating` |
| 0317786bea4d | 221–223 thm:full-defect-ring for every n ≥ 2 | formalized: `manuscriptPrintedFullDefectRingProgrammeAllCharacteristics` | GAP (carrier generality): the programme's theorem clause is `PrintedFullComplementaryIdempotents`, n ≥ 4. The printed n ≥ 2 is `FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics : PrintedFullComplementaryIdempotentsRankTwo`, already closed and root-reachable. Fix: census row re-pointed, no new Lean |
| 4bf35a8f555d | 225–231 L_{F₂}(1,2) and eq:leavitt | definition: `FullDefectRingSentences.manuscriptSentence_ringRelations` | DEFECT (wrong carrier): that theorem is the relation list of 𝒞 in the proof of thm:full-defect-ring, not the definition of the binary Leavitt algebra. Correct carriers: `BinaryLeavitt.Relation` (the five equations of eq:leavitt), `BinaryLeavitt.BinaryLeavittAlgebra` (the `RingQuot` presentation), `BinaryLeavitt.family`, `BinaryLeavitt.lift`, `UniversalLeavitt.BinaryLeavittAlgebra` (the F₂ specialization). Fix: census row re-pointed |

`\cite{Leavitt}` at tex 226 names the algebra; it is not used as a proof step.

## Progress log
- 16:55 ledger landed; module claimed.
