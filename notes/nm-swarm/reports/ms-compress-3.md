# Lane ms-compress-3: tex 583–657 (cor:defect-hs, "From Hilbert--Schmidt to operator norm", lem:central-corona-corner)

Lead: session nonsofic-existence-49 (wave 2). Snapshot: origin/main 62471b165 (09-13 ~16:40). Tex line numbers are at
68481e4d7. Census rows are keyed at the pre-chain-core hash (census line ≈ tex line − 11 here), so they are matched by text.

## Sentence ledger

| tex | sentence (abridged) | key | status | carriers | verdict |
|---|---|---|---|---|---|
| 584 | Let L ≤ G have (T) and (V_n) an operator norm asymptotic representation | 67ab9f71cba9 | structural | hypotheses of `PrintedDefectHS` | OK (hypothesis sentence) |
| 587 | ‖V_n(d) − 1‖₂ → 0 for d ∈ 𝔇_G(L) | c36b6021a802 | formalized | `PrintedDefectHS` / `manuscriptPrintedDefectHS` (PrintedForms), `CompressionDefectHSInvisible`, `hsVanishes_of_mem_printedDefect` | PASS: ∀ G, L with (T), ∀ OpAlmostRepresentation B, ∀ d ∈ `printedDefect L` (= normal closure of [ucu⁻¹, ℓ], `eq:intrinsic-defect` verbatim), `HSVanishes B d` = √(hsNormSq (V_n(d) − 1)) → 0 |
| 595 | Let uLu⁻¹ ≤ L, c ∈ C_G(L), ℓ ∈ L; write 𝒞₂ = 𝒞₂(V, L) | 2a0e1987e5c2 | structural | — | OK (notation) |
| 596–599 | (V_n(c)) ∈ 𝒞₂, transport, (V_n(ucu⁻¹)) ∈ 𝒞₂ | 310f6df94cdf | formalized | `CompressionCriterionSentences.manuscriptSentence_conjugatedCentralizerStaysInPrintedCommutant` | PASS: three memberships at `boundedHSCommutant` (where thm:transport is an equality) and again at the printed `printedCTwo` (HS-bounded ∧ HS asymptotically central) |
| 600–601 | HS commutator → 0; ‖V_n([ucu⁻¹, ℓ]) − 1‖₂ → 0 | a6988bc68f49 | formalized | `manuscriptSentence_hsCommutatorVanishesAndDefectIsHSTrivial` | PASS |
| 602–603 | these elements form a normal subgroup containing 𝔇_G(L) | acc79ac4eb5f | formalized | `manuscriptSentence_hsTrivialElementsFormNormalSubgroupWithDefect` | PASS |
| 608–616 | HS smallness does not bound the operator norm: D_d, ‖D_d − 1‖₂ = 2/√d → 0, ‖D_d − 1‖ = 2 | f4cdb1554874 | formalized | `NonMFSentences.manuscriptSentence_hsSmallnessDoesNotBoundOperatorNorm`, `printedSignDiagonal` | PASS (every d ≥ 1, unitary, both norms, the limit) |
| 617–619 | a vanishing-fraction corner can carry the entire obstruction; hence renormalize by rank | a1f7e96658eb | structural | — | GAP (mild): the first clause is a mathematical assertion. CLAIM below |
| 621–625 | restricting ρ to a corner needs a correction; q_n commute only asymptotically with U_n(g); compressions only approximately unitary | c9d3bf1f96b3 | formalized | `manuscriptSentence_cornerCompressionsAreOnlyApproximatelyUnitary` | PASS for the positive clauses (asymptotic commutation, Gram defect ≤ commutator², polar correction). The word "only" has no witness; recorded, not claimed |
| 628–630 | ρ : G → U(𝒬_d) from a countable group, q nonzero projection commuting with ρ(G) | 2aa506733448 | structural | hypotheses of `PrintedCentralCoronaCorner` | OK |
| 630–636 | discard the coordinates where a fixed projection lift vanishes; infinitely many remain; ranks r_n ≥ 1, identification q𝒬_d q ≅ 𝒬_r, W_n with corona homomorphism g ↦ qρ(g) | b0058fab44d8 | formalized | `CentralCoronaCornerPrintedRoute.manuscriptPrintedCentralCoronaCorner`, `manuscriptCentralCoronaCorner` | GAP: both endpoints assert the conclusion on SOME strictly increasing subsequence of nonvanishing coordinates of SOME projection lift, with 0 < card r_k. The printed statement fixes a projection lift, keeps EXACTLY its nonvanishing coordinates, and the r_n are the ranks. The proof builds exactly that (`Nat.nth`), but neither endpoint records it. CLAIM below |
| 642 | lift q to projections q_n by functional calculus | 4c8affbaad3c | formalized | `CollapseProjectionLift.exists_projection_lift` (Hermitian lift, then spectral rounding `roundSeq`) | PASS |
| 643–644 | infinitely many q_n nonzero; retain those; r_n = rank(q_n) | f494ded864dc | formalized | `NonMFSentences.manuscriptSentence_retainedCoordinatesAndRanks`, `manuscriptSentence_retainedCoordinatesInfinite` | PASS (range of `Nat.nth` = nonvanishing set; card of the corner model = rank) |
| 644–648 | corner identifications give q𝒬_d q ≅ 𝒬_r: (z_n) ↦ (q_n z_n q_n) | 6a04faf78706 | formalized | `CornerCoronaEmbedding.cornerEmbedSeq_*`, `norm_mk_cornerEmbedSeq` | PASS |
| 648–651 | g ↦ qρ(g) is a homomorphism to the unitary group of the corner, unit q | b0bfcbaafc1f | formalized | `exists_cornerUnitaries` | PASS (the corner-valued hom `tau` inside the proof; statement gives W and the class equation) |
| 651–653 | each value lifts to unitaries W_n(g), W_n(1) = I (as in lem:stable-finite) | dd524ef78e79 | formalized | `exists_cornerUnitaries` via `CollapseUnitaryLift.liftFam` | PASS |
| 654–655 | multiplicativity in the corona makes (W_n) an operator norm asymptotic representation with corona hom g ↦ qρ(g) | 87860427644c | formalized | `exists_cornerUnitaries` | PASS |

Root closure (import walk at origin/main): all eleven carrier modules are reachable from `GroupApproximation.lean`
(DefectHS, PrintedDefectShadow, PrintedForms, HSVanishesProducers, CompressionCriterionSentences,
NonMFSentences.CentralCoronaCornerRanks, NonMFSentences.HSOperatorNormGapSentences, CentralCoronaCorner,
CentralCoronaCornerPrintedRoute, CornerCoronaEmbedding, Analysis.CollapseProjectionLift).
`#audit_closed_axioms` lines exist for the four endpoints (Endpoint/OneSidedTransportAudit, Manuscript/NonMF/Audit/Sec2,
Manuscript/OneSidedMFRadical/Audit, and the route module itself). No literature binder in any chain above.

Hygiene only: `CentralCoronaCornerPrintedRoute.lean`'s module docstring quotes an earlier wording of the printed proof
("Unitary identifications J_n …"). The route is unchanged.

## Claims

- CLAIM lem:central-corona-corner exact endpoint: `GroupApproximation/Manuscript/OneSidedMFRadical/CentralCoronaCornerExact.lean`
  (`PrintedCentralCoronaCornerExact`). For EVERY projection lift Q of q, with φ = `Nat.nth` of its nonvanishing set:
  `Set.range φ = {n | Q n ≠ 0}`, `card (r k) = rank (Q (φ k))`, plus every clause of `PrintedCentralCoronaCorner`.
- CLAIM the vanishing-corner sentence (a1f7e96658eb): same new module family, `NonMFSentences/HSOperatorNormGapCorner.lean`.

## Progress log
- 16:5x ledger landed; building the exact endpoint.
