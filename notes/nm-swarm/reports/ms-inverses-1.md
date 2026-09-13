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

## Progress log
- 16:5x: ledger landed; two gaps (rows 2 and 9) claimed.
