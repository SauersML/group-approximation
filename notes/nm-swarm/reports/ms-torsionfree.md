# Lane ms-torsionfree: sentence ledger for tex 2107–2507

This covers sec:torsion-free, Origin and authorship, Acknowledgments and the bibliography.

- Snapshot: origin/main 5b3910136. The tex is byte-identical to 68481e4d7.
- Census source: `metadata/NON_MF_SENTENCE_CENSUS.tsv`, with 53 rows in range.
  - Every row's sentence text occurs verbatim in the current tex.
  - A sentence split of tex 2107–2273 finds no sentence without a row.
- Row `4ce81a3db24b` ("Apply Proposition prop:clifford-locally-rf to …") ends sec:amenable-nonqd, so it belongs to
  ms-traces-3.
- The bibliography (tex 2275–2506, 36 `\bibitem`) has no sentence rows. The use of each citation is ms-cite-2's sweep.

## Summary

| status | rows | verdict |
|---|---|---|
| formalized | 16 | all PASS |
| definition | 1 | PASS |
| structural | 3 | honest |
| provenance | 19 | honest |
| attribution | 2 | honest |
| partial | 12 | 11 bound to W1 (hgreendlinger); 1 regrade to formalized proposed (a9dd4b90e479) |

## Method

- Root reachability: an import-closure walk from `GroupApproximation.lean` at origin, 6530 modules. Every carrier module
  of a formalized or definition row is in the closure.
- Closure:
  - Closed endpoints carry `#audit_closed_axioms`, either in their own module or in `Manuscript/NonMF/Audit/Sec5.lean`
    (`manuscriptSimpleFactorInDefect`, `osinTheorem12Printed_unconditional`).
  - Sentence-level carriers take only data the printed proof has already reached at that point: the Fournier-Facio data
    `F`, the surjection `φ`, the finite-order lift clause of thm:hull, and ¬MF of `Q` from thm:torsion-free. None takes
    a cited theorem as a binder.
  - `manuscriptSentence_algebraSimpleUniqueTraceStableRank` has a variant with literature binders (`hDGO`, `hGO`). Its row
    also names the closed form `TorsionFreeAlgebraSentencesClosed.manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed`,
    which is built on the audited `dgoTheorem235Printed` and `gerasimovaOsinTheorem11Printed`.

## Formalized and definition rows (verified)

| key | sentence | carriers | verdict |
|---|---|---|---|
| 615720614d7a | "A subgroup is suitable if …" | `TorsionFree.Suitable` (AcylindricallyHyperbolic.lean:254) | PASS: both clauses of Hull Def 1.4 |
| c650b0a20b89 | "The subgroup N is normal, and it is infinite … so N is suitable." | `OsinCitedSentencesClosed.manuscriptSentence_saturationSuitableClosed`, `GGT.OsinPrinted.osinLemma71Printed` (both audited) | PASS (display nit below) |
| 24d44fae17ad | display Q = ⟨φ(g_i)⟩ ≤ φ(N₀) ≤ φ(N) ≤ Q | `manuscriptSentence_saturationDisplay` | PASS |
| c3246ffe1961 | "torsion-free by thm:hull … finitely presented …" | `saturationQuotientTorsionFree`, `saturationQuotientFinitelyPresented` | PASS (step carrier) |
| 02b6bf87400f | "Put S = tJt⁻¹." | `PrintedFournierFacioData.conjFactor` and the commutator lemmas | PASS |
| 26237422bf4c | "J and S are perfect." | `commutator_simpleFactor_eq`, `commutator_conjFactor_eq` | PASS |
| 8e8d5f3f8be0, d8d9d495865d | [tct⁻¹, ℓ] ∈ 𝔇; [S,S] ≤ 𝔇; S ≤ 𝔇 | `PrintedDefectParagraph.*` (`manuscriptSimpleFactorInDefect` audited) | PASS |
| 56f937d2ec19 | "N … nontrivial because S is." | `manuscriptSentence_theoremNormalClosureNeBot` | PASS |
| 9d87872de931 | Q infinite; (T) as a quotient | `theoremQuotientInfinite`, `theoremQuotientKazhdan` | PASS |
| da4a1c0beff4, d29816e1de56 | φ(S) ≤ 𝔇_Q(φ(Γ)); normal; = Q | `theoremDefectFunctorial`, `theoremDefectEqTop`, `TorsionFreeDefectNormalClosure.printedNormalClosureDefectEqTop` (audited) | PASS |
| eef4d274766e | Q and φ(Γ) have (T) | `theoremBothKazhdan` | PASS |
| 871771af6cba | homomorphisms to MF groups trivial; MF quotients trivial | `PrintedTheoremQuotientTrivial` := `manuscriptSentence_theoremQuotientTrivial` (audited) | PASS |
| 92115dd7edef | non-degenerate hyperbolically embedded subgroup; no finite normal subgroup | `osinTheorem12Printed_unconditional` (audited), `algebraTrivialFiniteRadical`, DGO chain | PASS |
| f2bf6328169e | DGO 2.35 and GO 1.1 | `..._closed`; `dgoTheorem235Printed`, `gerasimovaOsinTheorem11Printed` (audited) | PASS |
| b7b49212cd37 | separable, two unitaries, stably finite, not MF | `algebraSeparableGenerated`, `algebraStablyFinite`, `algebraNotMF`, `algebraNotCDEOperatorMF` | PASS (step carrier) |

Display nit (census lane): row `c650b0a20b89` also names `PrintedSaturationHullPair` and `PrintedHullCorollary57`, and
its map note quotes the NEXT sentence (Hull Cor 5.7 and Lemma 5.8, row `2d1cd22e5f49`). This is harmless; trim when
convenient.

- Structural rows `ad474b8983df` and `73a1e7bae0fd` (section outline) and `0a882030dcd9` (transition): honest.
- Provenance (19) and attribution (2) rows: honest.
  - Two provenance sentences narrate mathematics: `2b5a42f87cb2` (the maximal C*-algebra of a strictly compressed Kazhdan
    group is infinite) and `1778c11e19e3` ("proved in Lean that it is not MF").
  - Both are history. The claims are carried by the prop:max-infinite and thm:torsion-free rows.

## Regrade proposed (no W1 dependence)

`a9dd4b90e479`, "For an acylindrically hyperbolic group G, choose the generating set A provided by Hull [Theorem 3.12]":
**partial → formalized.**
- `HullCitationSentences.printedHullGeneratingSetLimitSet : PrintedHullGeneratingSetLimitSet`
  (`∀ G, IsAcylindricallyHyperbolicLimitSet G → Nonempty (HullGeneratingSet G)`) is closed and audited.
  - `HullGeneratingSet` has Hull 3.12(4)'s three fields: hyperbolic Γ(G,A), acylindrical, non-elementary.
- `HullTheorem312Lemma58.printedHullTheorem312` (all four clauses as one TFAE) is closed and audited.
- The former `hhard` input `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`
  (GGT/OsinLimitSetSpelling.lean:47) is a binder-free, root-reachable theorem.
- The row still names the conditional `TorsionFreeLimitSetNotion.manuscriptSentence_hullGeneratingSetLimitSet` (binder
  `hhard`). That keeps the accepted `inlined-statement` baseline line alive. Dropping it from the row retires that line.
- Row: `metadata/nm-census-rows/ms-torsionfree.tsv`.

## W1-bound partial rows (the other swarm's; ledger only)

- The remaining binder in every chain is `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}`
  (hgreendlinger).
  - Its residual waist binders and their owners are in the other swarm's roster.
  - The w1-binder-1..8 lanes attack them as second starts.
- hbridge, Kotowski–Ollivier and the Hyde–Lodha simple group are applied closed, per the rows' notes.

| key | sentence | carrier over hgreendlinger | row owner |
|---|---|---|---|
| 8aead549f1fe, 4895f03fdf5f | thm:hull statement | `TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger` | fff-periodic |
| bcc99703f838 | paragraph after thm:hull | `printedHullProofParagraph_of_greendlinger` | fff-periodic |
| 2f55113239ce | lem:saturation statement | `printedSaturation_of_greendlinger` | fff-periodic |
| 2d1cd22e5f49 | Hull 5.7 + 5.8 pair, "Hull's theorem again applies" | pair closed (`printedSaturationHullPair`, `printedHullCorollary57`, `printedHullLemma58`, audited); "again applies" = `printedSaturationPairAndHullAgain_of_greendlinger` | cite-hull, fff-periodic |
| 2f997e5af4e6 | apply thm:hull to N₀ | `printedSaturationApplyHull_of_greendlinger` | fff-periodic |
| 8097c371f35d | the Fournier-Facio paragraph | `fournierFacioParagraph_of_greendlinger` | fff-periodic |
| dab2f2bfe084 | G₀ as a Hull Cor 7.4 common quotient | `TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger` (see note) | cite-hull |
| 721da4c14d11 | apply lem:saturation to G₀ and N | `printedTheoremApplySaturation_of_greendlinger` | fff-periodic |
| 7b1fa3182135, 8b1ec28a0e73 | cor:regular-nonmf-algebra statement | `printedRegularNonMFAlgebra_of_greendlinger` | fff-periodic |

Note on `dab2f2bfe084`:
- `TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger` proves the same
  `HullCommonQuotientPrinted` over hgreendlinger alone, applying the closed hbridge (18682110d). The row already names it.
- The row also still names the two-leaf forms (`manuscriptSentence_hullCommonQuotient_of_leastAreaLeaves`,
  `hullOneStepStatement_of_leastAreaLeaves`, `printedHullCorollary74_of_leastAreaLeaves`). They keep two baseline lines
  (buried-conditional, open-predicate) alive.
- The row in `metadata/nm-census-rows/ms-torsionfree.tsv` drops them. The status stays `partial`.

When hgreendlinger closes, all eleven rows flip by applying the closed producer.

## C6′ leaf (W1 binder 4, `OsinTwoGonHoldsSectionStatement`), coordinator item 09-13 ~17:20

CLAIM lake pocket region from inner following `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketRegionInnerFollows.lean`

- Proposed to w1-binder-4 in one message (17:55), with no reply requested unless it objects.
- The leaf covers the inner branch of L2 plus L3 of w1-binder-4's report.
- Ownership check (17:50): nothing on origin, in the shared tree, in `$NM/drafts` or in any lane report builds a
  `PocketRegion` or an outer disc region from inner following.
  - hl-lemma46's report mentions only the inner disc (`toDiscRegion_of_followsBoundary`).
  - The pieces this lane consumes are landed: `IsNoncrossingClosedWalk.reverseMapAlpha` and
    `FirstTurnWalk.not_mem_sideFaces` (hull-select), `reclosed_euler` (hull-euler), `toDiscRegion_of_euler`,
    `toDiscRegion_of_followsBoundary`.
- Statement, stated before building:
  - `sideFaces M (w.reverse.map α) = sideOutside M w` for a noncrossing `w` on a planar map;
  - `PocketRegion.ofNoncrossingClosedWalkInner hw hout hin`:
    - faces = `sideFaces w`, inner cycle `w`, outer cycle `w.reverse.map α`;
    - inner disc from `toDiscRegion_of_followsBoundary`;
    - outer disc from `reclosed_euler` on the reversed walk, whose outer cycle is `w`.
- Why it matters: in the lake (Configuration B) the inner cycle follows while the outer does not.
  - `PocketRegion.outer` needs only a connected, χ-preserving reclosing of the complement, which the reversed walk
    supplies.
  - So `emptyTwoGonInput_holds`, `InnerDiscRegion.ofPocketRegion` and `P.listVal_inner_eq_one` fire in the lake.
- Model test: the labelled lake rose (`OsinPocketLakeLabelledModel.roseDiagram`, walk `[0,2]`).
- w1-binder-4 agreed (17:59) and takes a different leaf.

### LANDED 2d0b61555 (probe 0913-181235-23552 GREEN, BUILT and COMPILED both modules; unwired, queued for wiring)

Module `GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionInnerFollows`:
- `Surgery.MapCollapse.BoundaryCycle.followsBoundary_of_faces_eq`, `reclosedMap_euler_of_faces_eq`: transport along a
  face-set equality with equal cycles.
- `IsNoncrossingClosedWalk.WalkClass`, `exists_walkClass`: every dart is in the face class of a dart of the walk or of the
  reversed walk. The union is closed under α and σ, and the map is connected.
- `IsNoncrossingClosedWalk.sideFaces_reverseMapAlpha : sideFaces M (w.reverse.map α) = sideOutside M w` and
  `sideOutside_reverseMapAlpha`. One inclusion is `FirstTurnWalk.not_mem_sideFaces`.
- `IsNoncrossingClosedWalk.reclosed_euler_outer_of_innerFollows`: χ of the reclosed other side equals χ(M) when the inner
  cycle follows. This is `reclosed_euler` on `hw.reverseMapAlpha`.
- `IsNoncrossingClosedWalk.outerDiscRegion_of_innerFollows`, whose cycle is `w.reverse.map α` (rfl).
- `PocketRegion.ofNoncrossingClosedWalkInner hw hout hin`, with `_faces`, `_inner_cycle`, `_outer_cycle` and
  `_invDarts_outer`.
- `Surgery.InnerDiscRegion.ofNoncrossingClosedWalkInner hw hout hin hcells`, with `_faces` and `_region_cycle` (= walk,
  rfl). This is the disc region for w1-binder-4's `TwoGonMergeDiscInput`.

Module `GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionInnerFollowsModel`:
- `lakeInnerFollowsPocketModel : LakeInnerFollowsPocketModel` (`#audit_closed_axioms`). The builder fires on the
  labelled lake rose `[0,2]`: complement cycle `[3,1]`, while that outer cycle does not follow its boundary.

Axioms, from the build log: every audited declaration depends on [propext, Classical.choice, Quot.sound]. The log has
0 warnings or errors in either file and 0 `sorryAx`.

Residual for C6′ outside this leaf: the producer of `hw` and `hin`, or of outer following, for the two-gon pocket walk
(L1 and L2 of w1-binder-4's report), and `hno`/`havoid` (debt-conditional's `TwoGonWalkHyp`). No census rows: the
modules certify no printed sentence on their own.

## V4 waist leaf: `CellPocketCopyCleanBothOrdersStatement` (main's item, 09-13 20:30): NOT TAKEN, held by w1-binder-5

This is one of the four residuals of ms-cite-1's order assembly (da5b1466e). Its docstring names w1-binder-5 as owner, and
ms-cite-1 authored it.
- One message went to each of them (20:30), asking for a reply only if they hold it.
- Ownership check (20:30): nothing on origin, in the shared tree, in `$NM/drafts` or in any `.files` produced it.
- w1-binder-5 replied (20:3x) that it holds the statement.
  - It is the same producer as its current `cellPocketCopyClean`, retargeted to both orders, with the one-order form as
    a projection.
  - `hasCellPair_regionPairStep` has just probed in its `OsinPocketCellCopyProducer`.
  - The only external blocker is ms-intro-2's `exists_regionPairFree_of_invariant` (agreed, not landed).
  - A named residual standing in for that induction would only reshape the statement, so none is stated.
- This lane landed no claim and wrote no module. The notes below are left for the owner.

Correction to the stage list:
- The cell pocket `CellPocketWalk.CopyClean` has no outer field. Its fields are `cell_self_first`/`_second`, `cell_cell`,
  `regions` and `side_first`/`_second`.
- So w1-binder-6's outer, spur and side_outer stages and ms-binary's cell-hair `cell_self` belong to the section pocket's
  `PocketWalk.CopyClean` and are not used here.
- The relator-cell fields come from w1-binder-5's landed `CellEdgeSideThickening.copyClean_of_noDarts` (a426c4f1b):
  - no cell-edge dart gives `cell_self` and `cell_cell`;
  - no cell-side dart (ms-cite-2's `CellSideThickening`) gives the side fields.

Route (agreed step for step with w1-binder-5's):
- `S.diagram` is least area, from `Δ` through `S.equiv` (`OuterCellThickening.leastArea_of_oEquivalent`), so no
  relator word has value one;
- `exists_cellEdgeSideFree_pair`, then the region-pair thickening carrying the invariants;
- `regions_of_noRegionPairDart` for (a′, b′) and for (b′, a′), with `hmono := one_lt_length_or_of_regions`
  (ms-intro-2, 9e31aea90);
- `copyClean_of_noDarts` in both orders.

Model test (paper, done before the reply):
- (a) The reduction.
  - `copyClean_of_noDarts` has only one premise that depends on the order, `regions`, and `regions` for (b′, a′)
    follows from (a′, b′) by applying α to the dart.
  - The side fields of the two orders list different darts (`b′.sideFrom j′ ++ a′.sideFrom i′` against
    `a′.sideFrom j′ ++ b′.sideFrom i′`). So a copy clean in one order need not be clean in the other; only the
    family-wide invariants give both.
- (b) The region-pair step with the carried invariants, on the smallest configuration: two relator cells, and regions
  `a`, `b` joining them that share one side edge `w_j` between the G-faces `f ⊆ a` and `g ⊆ b`.
  - Doubling inside `f` adds a G-digon, so no relator face gains an edge. Cell-edge darts and relator values are
    unchanged.
  - The side dart of `a` becomes the new dart, and `α w_j` on `b` now faces the digon, so no cell-side dart is created.
  - Source and target indices move through `indexEquiv`, which keeps `HasCellPair`.
  - `w_j` disappears (`regionPairCount_lt`).
  - No counterexample found.

## Progress

- 09-13 ~17:15: ledger landed; regrade row for `a9dd4b90e479` landed. No carrier gap outside W1 in range.
- 09-13 ~17:55: C6′ leaf claimed (above).
- 09-13 ~18:17: C6′ leaf landed (2d0b61555).
- 09-13 20:30: resumed after the API outage. main assigned the V4 leaf `CellPocketCopyCleanBothOrdersStatement`.
- 09-13 20:3x: that leaf is held by w1-binder-5 (above). No claim, no module. Lane free.
