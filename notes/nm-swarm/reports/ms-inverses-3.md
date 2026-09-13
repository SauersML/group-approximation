# Lane ms-inverses-3: tex 930–1049 (thm:full-defect-ring, cor:simple-infinite-ring)

This lane belongs to the session nonsofic-existence-49 team (see `ct-lead.md`, wave 2). Snapshot: origin/main 15ab3ebe5.
Numbering is unchanged in this range since 68481e4d7. Census rows are keyed at manuscript hash e66db325.

CLAIM printed-route triviality chain for thm:full-defect-ring (universal group, rank two, all ranks, corollary composites)
`GroupApproximation/Manuscript/NonMFSentences/FullDefectUniversalRoute.lean`

## Ledger

The census has 33 rows for this range. Every sentence is present. Row `4515e83a1b91` holds two sentences, the first case
and the second case of the corollary proof; its cut drops the display `t₂(1-s₁t₁)s₂=1`, which is carried by
`OneSidedCorollarySentences.manuscriptSentence_leavittCaseSandwich`.

| key | sentence | status | carriers | verdict |
|---|---|---|---|---|
| 29118a9b250c | Let R be a countable unital associative ring. | formalized | FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics | PASS statement; ROUTE GAP (see below) |
| 5cbedadd4606 | Suppose that s,t ∈ R satisfy ts=1, R(1-st)R=R; | formalized | same | PASS statement; ROUTE GAP |
| 7ce8c636a470 | that is, 1-st is a full idempotent, so that 1=Σ a_j(1-st)b_j | definition | FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo | PASS (the Prop is stated through the printed gloss) |
| cede6c4edd2c | For every n≥2 … trivial. Every hom from EL_4(𝒞) … (T) … normally generates EL_n(R). | formalized | …RankTwoAllCharacteristics, UniversalGroupSigma.manuscriptFullComplementaryIdempotentsUniversal | PASS generality; ROUTE GAP |
| 469f1e197e95 | The universal group. In 𝒞 put s=s_0, t=t_0, e=1-st. | formalized | UniversalPair.pairInverse, UniversalGroupB.B | PASS (definitional) |
| a4cdcda5bef7 | Then ts=1, e²=e, es=te=0, t_1es_1=1. | formalized | FullDefectRingSentences.manuscriptSentence_ringRelations | PASS |
| a6ce75cd2625 | Put G=EL_4(𝒞), L=EL_3(𝒞) on coordinates 1,2,3. | formalized | manuscriptSentence_groupsGandL | PASS |
| 0939d33e1ff4 | 𝒞 nonzero, finitely generated; (T) by EJZ; EL_4(𝒞) f.g. by BHV | formalized | EJZCitationSentences.manuscriptSentence_universalRingBothGroupsPropertyT, UniversalRingSentences.manuscriptSentence_universalRingPrintedReasons | PASS: EJZ is the proved `ejz`; BHV is `KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT` |
| ade7fe9335db | By lem:ring-compression-cell there are u,c … d=e_13(e) ∈ 𝔇_G(L) | formalized | manuscriptSentence_compressorMatrix, manuscriptSentence_centralMark | PASS |
| ec86ceff1bf1 | Let N be the normal closure of d in G. | formalized | manuscriptSentence_normalClosureOfDefect | PASS |
| 8227dfc88059 | the Steinberg relations give … | formalized | manuscriptSentence_steinbergPair | PASS |
| eb7d6fe7334e | So e_42(1)=e_42(t_1es_1) ∈ N. | formalized | manuscriptSentence_fullnessRootRewrite | PASS |
| ad1cfff561d3 | signed permutation matrices … e_ij(1) ∈ N | formalized | ElementaryWeyl.elGen_one_mem_of_ne | PASS |
| 8830867a92de | [e_ij(1),e_jk(r)]=e_ik(r) ∈ N | formalized | manuscriptSentence_steinbergSpreadsCoefficients | PASS |
| c0333a70aec6 | So N=G, and 𝔇_G(L)=G. | formalized | manuscriptSentence_defectIsEverything | PASS; `manuscriptSentence_signedPermutationsReachEveryPosition` also carries N=G |
| 2e41521883fb | By thm:compression-criterion with K=G, every hom from G to an MF group is trivial. | formalized | manuscriptSentence_homFromBTrivial | ROUTE GAP: the carrier is `UniversalGroupB.hom_eq_one`, the rank-four endpoint at 𝒞 through descent to f.g. subrings, not the criterion at G with K=G |
| f840f9a0ef7c | Rank two. Now let R satisfy the hypothesis. | structural | — | PASS |
| 45f5c651c852 | By lem:two-copies choose v_i, w_i | formalized | manuscriptSentence_twoCopies | PASS |
| 2d95c1b6384d | φ: 𝒞→R unital, induces EL_4(𝒞)→EL_4(R) | formalized | manuscriptSentence_universalProperty | PASS |
| 546f936f3fbe, 53f2c41f65d9 | S_i, T_i; T_iS_j=δ_ij; p=ΣS_iT_i | formalized | manuscriptSentence_lengthTwoWords, manuscriptSentence_pIdem | PASS |
| 45c0a7a24b09 | ȷ(A)=1-p+ΣS_iA_ijT_j | definition | manuscriptSentence_jMapDef | PASS |
| 605dfb0242a3 | ȷ multiplicative, Ψ hom GL_4→GL_2, Ψ(e_ij(r))=… | formalized | manuscriptSentence_jMapMultiplicative, psiIsDiag, psiOnRoots | PASS |
| 18ab8ca8e9ef | by lem:rank-two, since T_jS_i=0 | formalized | manuscriptSentence_psiOnRoots | PASS |
| e440073f849c | So Ψ(EL_4(R)) ≤ EL_2(R). | formalized | manuscriptSentence_psiLandsInEL2 | PASS |
| 7fb55eb3f582 | Let ρ be a hom from EL_2(R) to an MF group. | formalized | manuscriptSentence_imageOfB | GAP: the carrier states triviality on EL_4(R) |
| 16a8406515ce | Composed with EL_4(𝒞)→EL_4(R)→EL_2(R) it is trivial, so ρ kills Ψ(e_12(1)) … normally generates EL_2(R) | formalized | manuscriptSentence_imageOfB | GAP: not the printed statement (see below) |
| 1a16fdba9df3 | So ρ is trivial, and the image of EL_4(𝒞) in EL_2(R) normally generates EL_2(R). | formalized | manuscriptSentence_rhoTrivial, …imageOfBNormallyGeneratesEL2 | ROUTE GAP: `rhoTrivial` takes the rank-four conclusion at R as the hypothesis `h4` |
| f6edc460fb1b | All ranks. signed permutations … copy of EL_2(R) normally generates EL_n(R) | formalized | FullDefectAllRanksSentences.manuscriptSentence_allRanksSignedPermutations | PASS |
| 8487a62c655f | A hom from EL_n(R) … trivial on that copy, hence trivial; image of EL_4(𝒞) normally generates | formalized | manuscriptSentence_homFromELnTrivial | ROUTE GAP: takes `h4` |
| a4b5b1a0504a | non-MF passes up from corners … | formalized | FullDefectCornerRemark.manuscriptSentence_cornerPassesUp | PASS |
| 34366ed3b6a0 | full-defect hypothesis need not pass to R … | formalized | FullDefectCornerRemark.manuscriptSentence_hypothesisNeedNotPass | PASS (explicit witness L_{F_2}(1,2)×F_2) |
| 97fcf1f9add1 | cor: countable simple unital not directly finite ⇒ EL_n homs trivial, n≥2 | formalized | …SimpleInfiniteRingRankTwoAllCharacteristics | PASS generality; inherits the ROUTE GAP |
| 017719ec2a80 | same for L_k(1,m), k countable field, m≥2 | formalized | …LeavittAlgebraFullDefectRankTwoAllCharacteristics | PASS generality; inherits the ROUTE GAP |
| 4515e83a1b91 | first case … second case … 1-s_1t_1=Σ_{i≥2}s_it_i [t_2(1-s_1t_1)s_2=1] | formalized | OneSidedCorollarySentences.manuscriptSentence_simpleCaseIdempotentFull, leavittCaseSandwich; OneSidedSentences.simpleRingChooseAndFull, leavittChooseAndFull | PASS |
| e490d00b41a0 | Theorem applies in both cases. | formalized | OneSidedSentences.manuscriptSentence_simpleInfiniteRingCorollaryStatement | PASS |

## The route gap

- The printed proof: B = EL_4(𝒞) kills MF targets by thm:compression-criterion with K = G (𝔇_G(L) = G, with L and G both
  Kazhdan by EJZ). Rank two then uses only the composite B → EL_4(R) → EL_2(R) and lem:rank-two. All ranks uses the copy of
  EL_2(R).
- The Lean chain on main:
  - reaches B's triviality through the rank-four theorem at 𝒞;
  - reaches the rank-two and all-ranks triviality through the rank-four theorem at R, via
    `FullDefectRankTwo.rankTwo_of_rankFour` and `hom_eq_one_of_rankFour` with the hypothesis `h4`;
  - proves that rank-four theorem by the pre-revision descent to finitely generated subrings (`FullDefectAtFixedRing`,
    `fullComplementaryIdempotentsOverSubrings_of_fixedRing`).
- Every declaration is closed and correct; only the route differs from the printed text.
- Fix (this lane): a module whose chain is B's triviality from `manuscriptSaturatedPrintedDefectRadical` at (B, core 𝒞),
  then ρ killing `toRankTwo Q (e_12(1)) = gen(S_1, T_2)`, then ρ trivial by `normalClosure_descent_root_eq_top`, then all
  ranks through the block copy. On top of that, the printed endpoints `PrintedFullComplementaryIdempotentsRankTwo`,
  `PrintedSimpleInfiniteRingRankTwo` and `PrintedLeavittAlgebraFullDefectRankTwo` are re-proved with no rank-four input
  at R.
