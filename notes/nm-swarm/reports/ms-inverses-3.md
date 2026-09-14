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

## Landed (72c47f30a, probe 0913-172821-62100 GREEN, verdict and BUILT lines checked)

- `GroupApproximation/Manuscript/NonMFSentences/FullDefectUniversalRoute.lean` carries the printed route:
  - `manuscriptSentence_homFromBTrivialByCriterion`: the compression criterion at `G = EL₄(𝒞)`, `L` = core, `K = G`.
  - `manuscriptSentence_rhoKillsImageOfB`, `manuscriptSentence_rhoTrivialByUniversalGroup`: rank two through
    `EL₄(𝒞) → EL₄(R) → EL₂(R)` and lem:rank-two.
  - `manuscriptSentence_homFromELnTrivialByUniversalGroup`, `manuscriptSentence_imageOfBInCopyNormallyGenerates`: all
    ranks through the copy of `EL₂(R)`.
  - Printed endpoints over that chain, with no rank-four input at `R`:
    `printedFullComplementaryIdempotentsRankTwo_byUniversalGroup`, `printedUniversalGroupClauses_byUniversalGroup`,
    `printedFullDefectRingTheorem_byUniversalGroup`, `printedSimpleInfiniteRingRankTwo_byUniversalGroup`,
    `printedLeavittAlgebraFullDefectRankTwo_byUniversalGroup`, `printedSimpleInfiniteRingCorollary_byUniversalGroup`.
- `GroupApproximation/Manuscript/NonMFSentences/FullDefectIdealGloss.lean` carries
  `manuscriptSentence_fullIdempotentGloss`: `1-st` is idempotent, and `TwoSidedIdeal.span {1-st} = ⊤` iff the printed
  finite sandwich sum exists.
- Census rows: `metadata/nm-census-rows/ms-inverses-3.tsv` (12 rows; the ROUTE GAP rows re-graded onto the new carriers).
- Wire queue: both modules appended to `$NM/wire-queue.txt`.

## Status of the range

Every sentence of tex 930–1049 now has a closed carrier along the printed route, or is structural.

## Item 2: lem:transient-matrices printed assembly (tex 1465–1508)

This item was assigned by main at ~18:45. chain-matricial is down; its `.files` holds only its three landed modules
(md5 equal to origin), so there were no drafts to finish.

### Landed

- **b421d0604**, `GroupApproximation/Manuscript/NonMFSentences/TransientMatrices.lean` (probe 0913-190708-24424 GREEN,
  verdict and BUILT lines checked):
  - `printedTransientMatricesIdealClauses` (closed). Over every finite field at `Y = CR(T)`, `I` is the kernel of
    restriction, `I = LC_c(X∖Y,k) ⋊_T ℤ` coefficientwise, `I` is locally matricial (ct-involution
    `transientIdealLocallyMatricialStatement_holds`, 49663bacb), and `I` is generated by the defects (ms-core-4
    `printedTransientIdealGeneratedByDefects`). No named premise.
  - `printedTransientMatrices_of_restrictSurjective : RestrictSurjectiveStatement → PrintedTransientMatrices`: the whole
    printed lemma, all five clauses.
  - Proof sentences (closed): `printedClosedSubsetExtension`, `printedRestrictionKernelCompactSupport`,
    `printedLaurentExactnessMiddle`; the lemma `mem_transientIdeal_iff_compactSupport`.
- **48794b1c1**, `GroupApproximation/Dynamics/ChainRecurrentPeriodic.lean`: `isChainRecurrent_of_isPeriodicPt` and
  the closed `printedTransientNoPeriodicPoints` (tex 1487, "Also U has no periodic points"). The sentence had no carrier
  and no owner.
- Both modules are queued in `$NM/wire-queue.txt`.

### Residual: surjectivity of restriction

`RestrictSurjectiveStatement` has one producer, in flight: ct-return-tower's `restrict_surjective_of_isClosed`
(`Manuscript/NonMFSentences/CoreRingReflection.lean`, attic e8daa265e, unlanded). It is a seven-line composite of on-main
lemmas (`Pestov91.CrossedProduct.coeffMap_surjective`, `ChainCore.LocallyConstant.exists_comap_val_eq_of_isClosed`). When
it lands, `printedTransientMatrices_closed` is one line: `printedTransientMatrices_of_restrictSurjective fun _ _ _ _ _ T k _
_ hY hYc => restrict_surjective_of_isClosed T k hY hYc`. Rows 7ff20576d4cf and 97e43ae93d14 then become formalized.

### Census rows (`metadata/nm-census-rows/ms-inverses-3.tsv`, 22 new rows)

- **formalized (12):**
  - carriers from this landing: f0c16e5c8519, 910136e6e66d, c05b0ec8b821, 4244fb3c658b;
  - carriers already on main: f5264e48f943, 1687471008a1, 741b64286b55, d01cbef361ce, 2a63696d979b, e55132ef58f5.
- **definition (2):** eda117e756e6 (locally matricial), e60c16639f70 (U = X∖Y).
- **partial, waiting on surjectivity (2):** 7ff20576d4cf, 97e43ae93d14.
- **partial, different route (8):**
  - 34e1eeff13be: the Laurent form, no graph decomposition;
  - cd20a742dd3c: C is a clopen containing the sources and ranges, not their union;
  - ff376e50f433: stabilization of reachable sets, not loop erasure;
  - a3598c08b42c: uniqueness from ExponentBound, not freeness;
  - 1d0f9a56866c: no separating partition;
  - fd026a61f84f: least exponent, not the first occupied atom;
  - 46f3810145ee: clopen for a different reason;
  - 5079b22a3633: refined by class exponents and values, with no atoms.
- 2546c17d9884 already carries ms-core-4's formalized row.

### Why ct-involution's rows stay partial

All three are printed steps of lem:involution-localization that reuse the finite matrix-block construction of
lem:transient-matrices, "refining also by K and C" (tex 1678–1680). The Lean chain reuses neither the classes nor the
representative cells.

- **07ab0fbe6cfc (tex 1678–1680):** `Dynamics.exists_returnPlacement` builds a piecewise placement over the wandering cover
  of K; the matrix-block construction is not run a second time, refined by K and C. There is also nothing for the
  refinement to act on: the Lean transient-matrices construction has no atom partition and uses least-exponent
  representatives (rows 1d0f9a56866c, fd026a61f84f above).
- **3468c60b2946 (tex 1681–1682):** the 2m distinct return points of each point are `card_returns_ge`, but no generated
  class is formed on the placement route, so "each generated class contains an original point and its 2m return points"
  has no class to attach to.
- **6baf73489057 (tex 1685–1686):** the matching is constant on the clopen cells `A j h`, a finite clopen partition of K.
  These are not the representative cells of lem:transient-matrices, since the printed "representative cell" of that
  construction does not exist on the Lean route.

### Closed (6867e7460, probe 0913-194044-12893 GREEN, verdict and BUILT lines checked)

ct-return-tower landed `ChainCore.CoreRingReflection.restrict_surjective_of_isClosed` at 17817cdac.
`GroupApproximation/Manuscript/NonMFSentences/TransientMatricesClosed.lean` discharges the premise by name:

- `restrictSurjectiveStatement_holds : RestrictSurjectiveStatement`;
- `printedTransientMatrices_closed : PrintedTransientMatrices`, the printed lemma with all five clauses, closed;
- `printedLaurentExactness`, exactness at both ends (tex 1481).

It is a separate consumer module, so `TransientMatrices` does not import `DynamicRankBudget`.  No import cycle: nothing on
origin imports `TransientMatrices`.

Rows 7ff20576d4cf and 97e43ae93d14 are now formalized.  Every sentence of tex 1465–1508 has a row: 14 formalized,
2 definition, 8 partial for route differences (reasons in the rows), and 2546c17d9884 carried by ms-core-4's row.

## Item 3: printed-route carriers for the route-difference rows of tex 1485-1505

CLAIM partial-shift graph decomposition, union of sources and ranges, freeness => unique arrow (rows 34e1eeff13be, cd20a742dd3c, a3598c08b42c) `GroupApproximation/Dynamics/TransientPartialShiftGraphs.lean`
CLAIM separating partition, first-occupied-atom representative, clopen representative set, refinement by occupied atoms, loop erasure (rows 1d0f9a56866c, fd026a61f84f, 46f3810145ee, 5079b22a3633, ff376e50f433) `GroupApproximation/Dynamics/TransientAtomRepresentatives.lean`

### Result (23:2x): route-difference rows of tex 1485-1503

- LANDED 1684652bd `GroupApproximation/Dynamics/TransientPartialShiftGraphs.lean` (probe 0913-213245-30245 GREEN, BUILT).
  The first probe 0913-203849-76048 was red (DecidableEq k, a section binder); its `.green.` record is the mixed-record artifact.
  - `printedPartialShiftGraphExpansion` (tex 1487-1489): every x in I is sum_g sum_{c ne 0} c 1_{D_{g,c}} u^g, domains compact clopen off CR(T).
  - `printedSourceRangeUnion` (tex 1489-1490): C is the union of the sources and ranges of the graphs and their inverses; clopen, compact, off CR(T), carries every coefficient.
  - `transientCellsStatement_sourceRangeUnion`, `transientIdealLocallyMatricialStatement_sourceRangeUnion`: the cells and local matriciality over that C, closed.
  - `Dynamics.printedFreenessUniqueArrow` (tex 1492-1493).
- Finding: `exists_clopen_support` on main already builds its K as exactly this union, inside the proof. The old reason on cd20a742dd3c (not their union) described the statement, not the construction.
- Flipped to formalized: 34e1eeff13be, cd20a742dd3c, a3598c08b42c.
- Kept partial, reasons tightened in the rows:
  - ff376e50f433: loop erasure needs a path representation of reachableExponents, not on main;
  - 1d0f9a56866c, fd026a61f84f, 46f3810145ee, 5079b22a3633: the atom route needs the tower rebuilt over atom representatives, since TransientTowerFamily and TransientTowerExpansion are keyed to least-exponent ones.
- Queued for wiring at 1684652bd.

## Item 4: polygon-level bad-junction exclusion (main's item 23:12)

CLAIM polygon-level bad-junction exclusion for ms-binary's class producer (`OsinLemma94BadJunctionInput`, Estimating/OsinLemma94ClassJoins) `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94BadJunctionExclusion.lean`

Definitions, as ms-binary adopts them unchanged from ms-core-2's draft `Estimating/OsinLemma94ClassProducerGaps.lean`:
`junctionGap`, `ClassJoins := KindJoins ∧ value one ∧ (cell: gap misses the polygon face) ∧ (boundary: idxOf e < idxOf e')`,
`badJunctions := KindJoins ∧ ¬ClassJoins`.

Hand model tests (23:3x):
- **Cell face clause, always true on a planar map.** The gap darts are `α (facePerm^(t+1) a)`, `t < m`, and the polygon face is
  `faceOf (α b)`, so `JunctionPocket.gap_alpha_faceOf_ne` gives it. `hface` is `face_not_cell`, and `m = 0` leaves the gap empty.
- **Cell value clause.** The gap is a closed walk at the corner.
  - (i) Pocket side off the exterior with G-faces only: value one, but `closedWalk_value_eq_one_of_gCells` needs a `FaceAssembly`
    (general `RegionFaceAssemblyStatement` is an unproved binder).
  - (ii) Pocket with a relator cell: the loop-cut kill `false_of_pocketRegion_of_below` (binder `GeodesicCollarStatement`).
  - (iii) Exterior on the gap side: the polygon lies in a hole of cell j and the gap runs the long way, with value conj(val r_j) ≠ 1.
    A genuine bad junction, at most one per face (`reach_face_or_reach_face`, C1).
- **Lobe model for (iii), against summing over all `relatorPolygons`.** Take n = 1 and a cell carrying L G-triangle lobes, each next
  to an unselected polygon.
  - ms-binary's scope finding: the un-pinch does not raise the weight there, so the lobes stay polygons.
  - Each lobe is a one-side polygon of kind `cell j`. Its self-junction has gap = the rest of r_j, value ≠ 1 (`cell_listVal_ne_one`).
  - So Σ over `relatorPolygons` of `#badJunctions` ≥ L, unbounded at n = 1.
  - Lobes are single-class, not budget polygons. With the index set restricted to polygons with at least two class non-joins
    (⊇ `Q.budgetPolygons`, since `classCount ≤ max 1 #¬ClassJoins`), the lobes drop out.
  - hull-component's spur-in-a-bubble counter-example to that filter needs a pendant spur, removed under `S.DartMinimal`.
- **Boundary clauses.**
  - Backward junction (`idxOf e' ≤ idxOf e`): only at the base corner of `outerDarts` with one section (`count = 1`), so at most one.
  - Value clause: the gap is a lobe of `∂Δ` at a pinch vertex. It is bad only when the lobe carries a relator cell. Nested lobes seen
    by relator polygons use distinct cells between levels, and disjoint lobes seen by one polygon use distinct cells, so at most 2n.
- Spelling proposal sent to ms-binary (one message): same definitions, index set filtered to at least two class non-joins.

### audit-nm-4 generality finding on f5264e48f943 (01:2x), fixed

- Finding (audit-nm-4, merge 0e622f840): the printed step covers a compact C ⊂ U, but the carrier
  `exists_wandering_clopen_cover` covers a clopen K only.
- LANDED 297e2dfc0 `GroupApproximation/Dynamics/TransientCompactWanderingCover.lean` (probe 0914-014300-2597 GREEN, BUILT).
  - `exists_isClopen_superset_subset_of_isCompact`: a compact C inside an open U of a compact zero-dimensional Hausdorff
    space lies in a clopen K ⊆ U.
  - `exists_wandering_clopen_cover_of_isCompact`, closed endpoint `printedCompactWanderingCover`: the wandering clopen
    cover and `ExponentBound T C m` for every compact C off CR(T).
- Row f5264e48f943 stays formalized, now naming these carriers. It supersedes audit-nm-4's proposed `partial` override.
- Queued for wiring at 297e2dfc0.

### Bad-junction exclusion: state at 02:0x

- Spelling agreed with ms-binary: `OsinLemma94BadJunctionInput` sums over `relatorPolygons.filter (2 ≤ #¬ClassJoins)`.
- Draft attic 81a7ace3a, `Estimating/OsinLemma94BadJunctionExclusion.lean`:
  - planar cell face clause `junctionGap_faceOf_ne_face`, closed endpoint `osinLemma94JunctionFaceClause`;
  - bad same-cell junctions = value failures (`listVal_junctionGap_ne_one_of_mem_badJunctions`);
  - reduction to boundary bad junctions (`sum_card_badJunctions_le_sum_boundaryBad`);
  - residual Props `OsinLemma94CellJunctionValueInput` and `OsinLemma94BoundaryJunctionBudgetInput`.
- Unprobed: it imports ms-binary's adopted `ClassProducerGaps`, not on origin at 02:02 (last attic 3f4fe3617). The
  overlay rule bars peer files, so the probe waits for that landing.

### Bad-junction exclusion, part 1 landed (ad307e323, probe 0914-083853-35124 GREEN, verdict and BUILT lines checked)

`GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94BadJunctionExclusion.lean`, over ms-binary's landed
`OsinLemma94ClassProducerGaps` (0011fcb93, definitions unchanged from ms-core-2's draft).
- `facePerm_getLast_eq_head_mod`: consecutive sides read cyclically, including the wrap from the last side to side 0
  (`facePerm_getLast_last_eq_head_zero`, through `Embedded.isChain_rotate_closing`).
- `alpha_mem_cellDarts_of_mem_sideDarts`: the reverse of a dart on a `cell j` side is a dart of cell j.
- `junctionGap_faceOf_ne_face`: at every kind-level same-cell join, no gap dart lies on the polygon face. Proved at the
  polygon corner through hull-component's `JunctionPocket.gap_alpha_faceOf_ne`, on the planar optimal diagram. Closed
  endpoint `osinLemma94JunctionFaceClause : OsinLemma94JunctionFaceClauseStatement`.
- `listVal_junctionGap_ne_one_of_mem_badJunctions`: a bad same-cell junction is exactly a gap word of value ≠ 1.
- `card_badJunctions_le_boundaryBad`, `sum_card_badJunctions_le_sum_boundaryBad`: once same-cell gaps have value one,
  the bad junctions are the boundary bad junctions (`boundaryBadJunctions`).
- Residuals, stated with the binders of `OsinLemma94LongTransitionInput` over the agreed index set (spelled inline;
  respelled over ms-binary's `P.nonJoinPolygons` once `OsinLemma94ClassJoins` lands):
  - `OsinLemma94CellJunctionValueInput`: the gap of a kind-level same-cell join has value one;
  - `OsinLemma94BoundaryJunctionBudgetInput`: the boundary bad junctions number at most `K n`.
- Next: `osinLemma94BadJunctionInput_of_pieces`, i.e. `OsinLemma94BadJunctionInput` from the two residuals, once
  ms-binary's `OsinLemma94ClassJoins` lands. The module certifies no printed sentence, so no census rows.
- Queued for wiring at ad307e323.

### Split of the boundary budget and a correction (09:0x)

- ms-core-1 (assigned by main) produces `OsinLemma94BoundaryJunctionBudgetInput` with K = 3, in
  `Estimating/OsinLemma94BoundaryJunctionBudget.lean`, importing ad307e323. The split:
  - `P.boundaryBadJunctions k ⊆ backwardJunctions ∪ valueFailureJunctions`, closed. The two are disjoint, since a backward
    gap is `take 0 = []` with value one.
  - Residual pieces: `OsinLemma94BackwardJunctionCountInput` (≤ n + 1) and `OsinLemma94BoundaryValueFailureCountInput` (≤ n).
- This lane keeps `OsinLemma94CellJunctionValueInput`, the respell over ms-binary's `classNonJoins` / `nonJoinPolygons`, and
  `osinLemma94BadJunctionInput_of_pieces`.
- **Correction** to the model tests above: "Backward junction ... at most one" is false. ms-core-1's model has nested lobes
  L₂ ⊂ L₁ of ∂Δ, both containing index 0, with a relator polygon at each pinch, which gives two backward junctions.
  - What holds: at most one per polygon, and each nesting level carries a distinct relator cell, so at most n + 1.
  - The residual Prop has `∃ K`, so its statement is unaffected. Only the count in these notes changes.

CLAIM bridge from the two residuals to ms-binary's `OsinLemma94BadJunctionInput` (`osinLemma94BadJunctionInput_of_pieces`) `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94BadJunctionPieces.lean`
- Imports ms-binary's `OsinLemma94ClassJoins` (`nonJoinPolygons`, definitionally the inline index set of the landed
  residuals) and ad307e323. The landed residual statements are not respelled, so ms-core-1's import target is unchanged.

### Bridge landed (3b739a1ff, probe 0914-091636-15390 GREEN, verdict and BUILT lines checked)

`GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94BadJunctionPieces.lean`, over ms-binary's `OsinLemma94ClassJoins`
(efa471e68) and ad307e323.
- `osinLemma94BadJunctionInput_of_pieces : OsinLemma94CellJunctionValueInput → OsinLemma94BoundaryJunctionBudgetInput →
  OsinLemma94BadJunctionInput`, with ε₀ and ρ₀ the maxima of the two inputs and the boundary constant `K`.
- `P.nonJoinPolygons` unfolds to the inline index set of the landed residuals, so the residual statements stay unchanged,
  and so does ms-core-1's import target.
- Consumer chain: ms-binary's `osinLemma94ClassEndLoopsBudgetInput_of_joins` takes `OsinLemma94BadJunctionInput`, so
  clause (a) now waits on two things: ms-core-1's `OsinLemma94BoundaryJunctionBudgetInput` producer, and this lane's
  `OsinLemma94CellJunctionValueInput` (loop-cut kill, face assembly, and the hole-polygon filter).
- First bridge probe (0914-091249-70310) was red on a name collision:
  `OsinLemma94RealizedPolygons.alpha_mem_cellDarts_of_mem_sideDarts` is declared both in ad307e323 and in ms-binary's
  `OsinLemma94ClassJoinsCellArc`. This lane's copy is renamed `alpha_mem_cellDarts_of_mem_cellSideDarts` (declaration
  and its two uses), so `OsinLemma94BadJunctionExclusion` lands again with that one change. No other declaration
  collides (origin scan).
- Queued for wiring at 3b739a1ff.
