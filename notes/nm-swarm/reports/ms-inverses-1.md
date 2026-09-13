# Lane ms-inverses-1: tex 740–808 (prop:max-infinite, the remark after it, the opening of sec:one-sided-inverses)

Lead: session nonsofic-existence-49, wave 2. Range at origin/main 68481e4d7. The census line numbers in
`metadata/NON_MF_SENTENCE_CENSUS.tsv` are at the pre-chain-core manuscript (729–788), so rows below were matched by text.

CLAIM prop:max-infinite, literal proper isometry and diag amplification: GroupApproximation/Analysis/MaxInfiniteProperIsometry.lean

## Ledger

| # | tex | key | status | carriers | verdict |
|---|---|---|---|---|---|
| 1 | 741–742 | e934e8d15b65 | structural | `MaximalCStarPrintedHypotheses.manuscriptMaximalCStarRemarkFromPrintedHypotheses` | OK: hypothesis header |
| 2 | 742–743 | e681972f7114 | formalized | same endpoint; `QuasiRegularWitness.baseVector_apply_base`; `manuscriptProperIsometryStrictOrder` | GAP: no closed declaration states "C*max(G) contains a proper isometry" at the printed hypotheses. The endpoint gives `¬ IsDedekindFiniteMonoid`; `manuscriptProperIsometryStrictOrder` is about an abstract C*-algebra with `p < u p u*`. Claimed above. |
| 3 | 743–745 | a45c53bf93dd | formalized | same endpoint | OK: not stably finite, no faithful tracial state, not RFD, not MF; closed (audited in Manuscript/NonMF/Audit/Sec2.lean); drops countability, which is more general |
| 4 | 752–754 | 0546c4f445c0 | definition | `KazhdanData.projection`, `StrictKazhdanCompression.proj`, `.shift` | OK: the Kazhdan projection is built as the spectral projection of the orbit average at the isolated point 1, and `exists_kazhdanData` gets it from (T); no Akemann–Walter binder |
| 5 | 755–759 | 9b21786b2a7b | formalized | `conjugate_mul_proj`, `proj_mul_conjugate`, `manuscriptMaximalCStarKazhdanProjectionOrder` | OK: closed (audited in Audit/Intro.lean and Endpoint/OneSidedTransportAudit.lean) |
| 6 | 759–763 | f67f0ad4466e | formalized | `baseVector_apply_base`, `conjugate_ne_proj` | OK |
| 7 | 763–764 | f6355addf8b7 | formalized | `ProperProjectionCompression.{p_mul_q, q_mul_p, p_mul_star_u_mul_one_sub_q, isometry}` | OK |
| 8 | 765–767 | 0d4f7970ddf4 | formalized | `star_isometry_mul_isometry`, `isometry_mul_star_isometry` | OK |
| 9 | 768–770 | 901f1b49e4e9 | formalized | `isometry_mul_star_ne_one`, `not_isStablyFiniteRing` | GAP (proof step): "diag(s,1,…,1) is one in every matrix algebra over C*max(G)" has no carrier. Claimed above. |
| 10 | 770–772 | 99f6411ca7a5 | formalized | `no_faithfulTracialState` | OK |
| 11 | 772–774 | e4fcef4295ca | formalized | `MatrixCoronaFinite.mfAlgebra_isStablyFinite`, `ResiduallyFiniteDimensionalMF.isMFAlgebra` | OK: both proved; RFD ⇒ MF uses a countable separating family into a bounded matrix product, with no [BK] binder |
| 12 | 777–778 | f979bf757c44 | formalized | `MaxInfiniteConverse.manuscriptMaxInfiniteConverseRemark` | OK: closed (module audit and Audit/Sec2.lean) |
| 13 | 778–791 | 07642b10d3ee | formalized | `AffineHNNBase.{manuscriptSentence_ascendingHNNMatrixRealization, realization_injective, range_realization}` | OK |
| 14 | 792–793 | 330d435b12e2 | formalized | `manuscriptSentence_reductionModuloOddRFAndMF`, `...Separates`, `reductionHom`, `dyadicReduceHom` | OK: closed; MF comes from `isOperatorMF_of_residuallyFinite`, with no Korchagin binder |
| 15 | 793–795 | 7d36ccc6e758 | formalized | `MaxInfiniteConverse.isOperatorMF`, `CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF` | OK: closed |
| 16 | 800–805 | 19abb698ab4a | structural | `hasKazhdanPropertyT_viaEJZ`, `manuscriptSentence_finitelyGeneratedGivesPropertyT` | OK: roadmap sentence; the mathematics is carried by thm:full-defect-ring rows |
| 17 | 805–807 | 3a929e3e1455 | structural | `OneSidedCompressor.compressor`, `compressor_compresses_core` | OK: roadmap sentence |

Definitions checked: `HasKazhdanPropertyT` is the Kazhdan-pair form over real Hilbert spaces, and `MaximalGroupCStar` is
the closed star subalgebra of the bounded product over all same-universe unitary representations. Neither assumes an
external existence theorem.

## Closed

- **Rows 2 and 9 CLOSED at 88180a8b8** (probe 0913-165710-37455 GREEN, BUILT line checked). Module
  `GroupApproximation/Analysis/MaxInfiniteProperIsometry.lean`:
  - `MaxInfiniteProperIsometry.PrintedMaxInfiniteProperIsometry` and the closed
    `manuscriptMaxInfiniteProperIsometry` (`#audit_closed_axioms`). For every G, every (T) subgroup Γ and every t with
    tΓt⁻¹ ⊊ Γ, there is s ∈ C*max(G) with s*s = 1 and ss* ≠ 1, and for every n, diag(s,1,…,1) ∈ M_{n+1}(C*max(G)) has
    both properties. s is the printed P u* + (1 − q).
  - `diagEntries`, `diagAmplification`, `star_diagAmplification_mul_self`, `diagAmplification_mul_star_ne_one`
    (`#audit_axioms`).
  - Queued for wiring. Rows are in `metadata/nm-census-rows/ms-inverses-1.tsv`.

- **Row 5 CLOSED at 696c4f2ac** (probe 0913-174153-16447 GREEN, BUILT line checked). Module
  `GroupApproximation/Analysis/MaxInfiniteConjugateKazhdanProjection.lean`:
  - `MaxInfiniteConjugateKazhdanProjection.PrintedConjugateKazhdanProjection` and the closed
    `manuscriptConjugateKazhdanProjection` (`#audit_closed_axioms`). For strict Kazhdan compression data:
    - conjugation by u sends the canonical unitary of ι(γ) to that of tι(γ)t⁻¹, which lies in tΓt⁻¹;
    - the average of the canonical unitaries of tΓt⁻¹ over the conjugated Kazhdan set has the Kazhdan gap;
    - its spectral projection is a star projection fixed by every canonical unitary of tΓt⁻¹;
    - uPu* equals that projection.
  - `unitary_conj_spectralProjection`: spectral projections are natural under unitary conjugation for gapped
    self-adjoint elements, proved algebraically (complements factor through 1 − u m u*), with no functional-calculus
    naturality. Main's existing conjugation lemmas need a normal subgroup.
  - Queued for wiring; row 9b21786b2a7b in `metadata/nm-census-rows/ms-inverses-1.tsv`.
- Every sentence of tex 740–808 is now carried or honestly classified.

## Binder 8

- main asked for one leaf of W1 binder 8, agreed with w1-binder-8. w1-binder-8 answered that steps 1–3 of StripStep,
  including the head-dart facts and the merged-face identification, are already drafted in its
  `SurgeryGeodesicCollarStripStep.lean`, and that nothing independent is left to split off. No leaf taken.

## Progress log
- 16:56: ledger landed at 1193c722d; two gaps (rows 2 and 9) claimed.
- 17:0x: both gaps closed at 88180a8b8.
- 17:4x: row 5 closed at 696c4f2ac. Binder 8: no independent leaf (w1-binder-8 owns steps 1–3).
