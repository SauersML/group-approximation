# lx-lhK-a — the Leray–Hirsch chart chain and the free-tuple ladder over a field K

Lane of the LIX strongest swarm (lead nonsofic-existence-39).  Clone `cs-endpoint` (shared with lx-lhK-b,
lx-integrator).  Owns `CharClass/LerayHirschChart*`, `LerayHirschGeneral*`, `ChartBundle*`, `ChartHomeo*`,
`ChartClass*`, `ChartTaut*`, `CohomologyChart*`, `MayerVietoris*`, `CohomologyDelta*`.  Agreed with lx-lhK-b
(09-12 ~10:40): this lane also owns the whole free-tuple ladder over K, i.e. `LerayHirschFreeExistsOf`,
`FreeTupleOf`, `FreeTupleExistsOf`, `LadderOf`, `LadderClosedOf`, `ProductOf`, and the `Col*Of`/`Tower*Of` glue.

Deliverable consumed by lx-lhK-b (compact Leray–Hirsch over K):
`LH.hasFreeTuple_cpProdOf (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ) (hd : 1 ≤ d + 1)
(hfib : Hmod K (CPtop (d + 1)) 2) (hfib0 : hfib ≠ 0) : HasFreeTuple (KnCP.cpFst U (d + 1)) (pull (KnCP.cpSnd U (d + 1)) 2 hfib) (d + 2)`.

## GREEN

Probe 0912-103112-83894 (cs-endpoint, acn112 64-71, base 4d86b2e8f), PROBE GREEN, 8991 jobs, all five `BUILT` + COMPILED,
first try:
- `LerayHirschChartGeneralOf` — `LH.LHOver_of_prodIsoOf (K) [CommRing K] f ξ U d V hfib hfree eX eP hsq hξ`.
- `LerayHirschChartBundleGenOf` — `LH.LHOver_chart_of_trivOf K p U r e hfib hfree ξ hξ`.
- `LerayHirschChartHomeoOf` — `LH.LHOver_chart_of_homeoOf K p U r h hbase hfib hfree ξ hξ`.
- `LerayHirschChartClassIsoOf` — `LH.cpCoordEmbOf`, `LH.fibClassOf K hgen r h` (Euler class rel. `hgen` of the
  tautological line of ℂP^r pushed along `Fin.castLE`: no cast in any statement), `fibClassOf_eq_pull_cpInclIter`,
  `fibClassOf_ne_zero`, `pull_prodIso_fibClassOf` (K-form of `pull_prodIso_cpGen`).
- `LerayHirschChartTautGenOf` — `LH.rank_le_one_add_tautCardOf`, `LH.hxi_trivOpenOf` (K-form of `hxi_trivOpen`).
Landed 772297d21, 354e358c5 (bytes = green record).

Probe 0912-110733-70338 (cs-endpoint, base 7b9e947aa), PROBE FAILED but COMPILED: `CohomologyChartTautClassOf`,
`CohomologyChartRankTwoInterfaceOf` (lhLowOf/lhSurjOf/lhUniqOf), `CohomologyChartSplitOf`, `CohomologyChartGenHypOf`.
Red: `LerayHirschProductOf` (missing import `LerayHirschColumnPack`, fixed), `CohomologyChartInductionOf` (nested pull in
`pull_sInclusion_cpPrCP_hOf` folded the wrong pair under `← pull_comp`, fixed by generalising the class; missing import
`CohomologyLHDegreewiseOf` for `KnHemi.pull_cohCastOf`, fixed).  Not reached: LowDegreeOf, PeelUniqOf, KunnethClosedOf.

## AUTHORED, UNVERIFIED (landed per rule 5')

- `CohomologyChartTautClassOf`: `interSigmaPtOf`, `cpTopPtOf`, `interSigmaOf_eq_pull`, `cpTopOf_eq_pull_cpTopPtOf`,
  `cpTop_cup_injective_zeroOf`, `cpTopPtOf_zero_ne_zero`.
- `CohomologyChartRankTwoInterfaceOf`: `cpTopPtOf_zero_eq_smul`, `cpTopOf_zero_eq_smul`, `lhLowOf`, `lhSurjOf`,
  `lhUniqOf` (against any nonzero `h ∈ H²(ℂP¹;K)`), helpers.
- `LerayHirschProductOf`: `LH.hasFreeTuple_of_bijective`, `LH.bijective_lhSum_cpProdOf`,
  **`LH.hasFreeTuple_cpProd_zeroOf K U hfib hfib0`** (unconditional rank two; lx-lhK-b's ring bootstrap consumes it).
- `CohomologyChartSplitOf`: `CPGenHypOf K e`, `CPSplitOf K e` (both for every nonzero class), flatness,
  `cpTop_cup_injectiveOf`.
- `CohomologyChartInductionOf`: `pull_punctIncl_hOf`, `pull_sInclusion_cpPrCP_hOf`, `pull_cpIncl_ne_zeroOf`,
  `eq_zero_of_mvResVOf_eq_zero_of_lt`, `exists_cup_gen_cpTopOf`, `cpSplitOf_one`, `cpSplitOf_succ`,
  `cpSplitOf_of_cpGenHypOf`.
- `CohomologyChartLowDegreeOf`, `CohomologyChartPeelUniqOf`, `CohomologyChartGenHypOf`
  (`cpGenHypOf_of_cupPowE_ne_zeroOf`), `CohomologyChartKunnethClosedOf` (`CPRingOf K`, `cpSplitOf_closed`, …).

## STATE AT 11:30 (HALT by lead: main gutted by becc912bd, restored forward at 3f71a3a50)

- AUTHORED on disk, NOT landed: the rank-2 and induction layers (TautClassOf, RankTwoInterfaceOf, ProductOf [import fixed],
  SplitOf, InductionOf [fixed], LowDegreeOf, PeelUniqOf, GenHypOf, KunnethClosedOf) and the whole tower (TowerOf, TowerFreeOf,
  TowerCollapseOf, TowerTopOf, FreenessOf).  Two landing attempts failed: the first push loop lost on non-fast-forward,
  then local ENOSPC; the third was refused because main lacked CohomologyChartFlatOf, then the HALT file.
- Probe 3 (tag 0912-112130-35613) ran on the gutted base bff8f642a before the warning arrived; killed.  cs-endpoint was left
  with 19 sources and `.nm/base = bff8f642a`; its 2768 oleans are intact.  The next probe at a restored tip delta-syncs all sources back.
- SPLIT adopted: lx-local2a took S1+S2 (adopted my FreeTupleOf draft, rewrote TowerSumOf), lx-stablyfinite took S3+S4
  (adopted my ColSumOf draft; `LerayHirschLadderClosedOf` gives `hasFreeTuple_cpProdOf K U d _hd hfib hfib0`, which
  lx-lhK-b's `LerayHirschCompactClosedOf` calls).
- WHEN THE HALT LIFTS: (1) land the fourteen files unverified (`msgs/lhKa-4.txt`); (2) ONE probe of ProductOf, InductionOf,
  LowDegreeOf, PeelUniqOf, KunnethClosedOf and Tower…Freeness at the restored tip; (3) fix reds; (4) land compiled bytes.

## NEXT (this lane, authoring now)

(11:45) All fourteen files LANDED UNVERIFIED at 3c6fbec99 (parent 933f34a60).  Spellings consumed by lx-local2a
(`peelTowerOf`, `exists_peelTowerOf`, `cupPowE_pull_eq_zeroOf`) and lx-stablyfinite (`CPRingOf`, `PeelFreeAtOf`,
`peelFreeAtOf K hring d`) checked against the landed bytes.  Probe 4 (tag 0912-113840-34864, cs-endpoint, base
2e6e6c1c0 = restored tree, 6235 sources, NM_CPUS=16) covers ProductOf, InductionOf, LowDegreeOf, PeelUniqOf,
KunnethClosedOf, TowerOf, TowerFreeOf, TowerCollapseOf, TowerTopOf, FreenessOf.  Then: fix reds in one batch (proof-only
fixes land at once; a statement change is announced to lx-local2a / lx-stablyfinite first), land compiled bytes.
Probe 4 result: PROBE FAILED.  BUILT/COMPILED: ProductOf, InductionOf, LowDegreeOf, KunnethClosedOf, plus TautClassOf,
RankTwoInterfaceOf, SplitOf, GenHypOf.  Red: `CohomologyChartPeelUniqOf:41` unknown `cpSliceGen_comp_cpPrCP` (declared
in the F₂ `CohomologyChartPeelUniq:66`); TowerOf…FreenessOf not reached.  Purge cleared 2447 artifact sets (mtime reset
by the restore sync).  Fix (import only) landed 577568a3a.  Cross-check: that lemma is the only F₂ chain name the Of
files use; none is redeclared.  Probe 5 (tag in `lx-lhK-a-probe5.out`) covers PeelUniqOf, TowerOf, TowerFreeOf,
TowerCollapseOf, TowerTopOf, FreenessOf.
The glue is NOT this lane's: `LH.lerayHirschGraded_compactOf` is lx-lhK-b's `LerayHirschCompactClosedOf` (on origin),
over lx-stablyfinite's `LerayHirschLadderClosedOf.hasFreeTuple_cpProdOf`, over lx-local2a's S1/S2 and this lane's tower.

## NEEDS

- lx-lhK-b: `CPn.cupPowE_ne_zeroOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) (h : Hmod K (CPtop d) 2) (h0 : h ≠ 0)
  {m : ℕ} (hm : m ≤ d) : cupPowE h m ≠ 0` in `ProjectiveSpaceRingClosedOf` (agreed; fills `KnCP.CPRingOf K`).

## TRAPS

- macOS BSD `sed` has no `\|` alternation in basic regex: a range `/a\|b/,$p` prints nothing.  Use `awk`.
- `git grep -E` has no `\b` (matches nothing); use `-w`.  zsh `$B:path` eats `:P`; write `${B}:path`.

## SPLIT (independent sub-tasks a helper could author in parallel; statements fixed now)

The tower statements this lane lands next, which the glue consumes (namespace `GroupApproximation.CharClass.KnCP`):
- `def peelTowerOf (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ) (h : Hmod K (CPtop (d + 1)) 2) (m : ℕ)
  (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) : (k : ℕ) → Hmod K (cpProdTop U d) (m + 2 * k)`
  `| 0 => pull (cpPrU U d) (m + 2 * 0) (a 0) | (k + 1) => pull (cpPrU U d) (m + 2 * (k + 1)) (a (k + 1)) + cup (peelTowerOf … k) (pull (cpPrCP U d) 2 h)`.
- `theorem exists_peelTowerOf K U d (hring : CPRingOf K) (h) (h0 : h ≠ 0) : ∀ (N : ℕ) (z : Hmod K (cpProdTop U d) N),
  ∃ (m k : ℕ) (_ : m < 2) (hN : m + 2 * k = N) (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)), z = cohCast hN (peelTowerOf K U d h m a k)`.
- `def PeelFreeAtOf (K : Type) [Field K] (d : ℕ) : Prop := ∀ (U : Type) [TopologicalSpace U] (h : Hmod K (CPtop (d + 1)) 2),
  h ≠ 0 → ∀ (m k : ℕ) (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)), peelTowerOf K U d h m a k = 0 → ∀ j, j ≤ k → k - j ≤ d + 1 → a j = 0`;
  `theorem peelFreeAtOf (K : Type) [Field K] (hring : CPRingOf K) (d : ℕ) : PeelFreeAtOf K d`.

S1. `CharClass/LerayHirschTowerSumOf.lean` (namespace LH): `lhTerm_index_congrOf`, `sum_cup_rightOf`, `lhTerm_succ_rightOf`
(generic `{K} [CommRing K]`, proofs = F₂ `LerayHirschTowerSum` verbatim), and
`peelTower_eq_sumOf K U d h m a k : KnCP.peelTowerOf K U d h m a k = ∑ i : Fin (k + 1), lhTerm (KnCP.cpPrU U d)
(pull (KnCP.cpPrCP U d) 2 h) (m + 2 * k) (k - (i : ℕ)) (cohCast _ (a i))`.  Inputs: `peelTowerOf` only.
S2. `CharClass/LerayHirschFreeTupleOf.lean`: `sum_lhTerm_range_leOf`, `towerCoeffOf`(+`_of_le`, `_of_gt`), `towerSumFunOf`,
`towerSumFun_eq_zero_of_gtOf`, `lhTerm_eq_zero_of_rankOf` (via `cupPowE_eq_zero_of_gt h (d+1) (hasCPCohomologyOf_CP K (d+1))`),
`towerSumFun_eq_zero_of_rankOf`, `towerCoeff_revOf`, `peelTower_eq_range_sumOf`, `sum_towerSumFun_range_leOf`,
`exists_freeTupleOf K U d hring h h0 n z` (F₂ `LerayHirschFreeExists` verbatim).  Inputs: S1, `exists_peelTowerOf`.
S3. `CharClass/LerayHirschColSumOf.lean`: `colTowerOf`, `colTower_ofOf`, `colTower_of_notOf`, `col_index_congrOf`,
`towerCoeff_colTowerOf`, `towerSumFun_colTowerOf`, `freeTuple_uniqueOf K U d hring h h0 n a hside hzero`
(F₂ `LerayHirschColTower/ColRead/ColSum` verbatim).  Inputs: S2, `peelFreeAtOf`.
S4. `CharClass/LerayHirschLadderClosedOf.lean`: `hasFreeTuple_cpProdOf K U d hd hfib hfib0` from S2, S3 and
`CPn.cupPowE_ne_zeroOf`.

## PROBE 5 GREEN (12:16)

Probe 0912-120703-48079 (acn112 slot 0, base 8a88f9ab6 + this lane's overlay, bytes = origin at 577568a3a / 3c6fbec99):
PROBE GREEN, 8985 jobs.  BUILT: PeelUniqOf, TowerOf, TowerFreeOf, TowerCollapseOf, TowerTopOf, FreenessOf.  The compiled
record `lanes/lx-lhK-a.green.0912-120703-48079` covers all fourteen files (probe 4 carries the BUILT lines of ProductOf,
InductionOf, LowDegreeOf, KunnethClosedOf).  `#audit` lines in the fourteen files: 0.
Unimported on disk at landing (wiring tops for lx-integrator):.
Consumers: lx-lhK-b `ProjectiveSpaceRingClosedOf` (ProductOf); lx-local2a S1/S2 (TowerOf, TowerTopOf); lx-stablyfinite
S3/S4 (FreenessOf); then lx-lhK-b `LerayHirschCompactClosedOf` = `LH.lerayHirschGraded_compactOf`.
