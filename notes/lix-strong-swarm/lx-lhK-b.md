# lx-lhK-b — compact Leray–Hirsch over a field K (successor of lix-lh, UNFINISHED section)

Clone cs-endpoint / lix-q (lead re-routed).  Owns every `CharClass/LerayHirsch*` except the chart chain
(`LerayHirschChart*`, `LerayHirschGeneral*`) and the free-tuple layer (FreeExists/FreeTuple/FreeTupleExists/
Ladder/LadderClosed/Product Of — ceded to lx-lhK-a by agreement), plus `Chern*` (not `ChernSplitting*`/
`ChernSplit*`/`ChernGamma*`), `Projective*`, `Bundle*`.

## Target
`LH.lerayHirschGraded_compactOf (K) [Field K] [CompactSpace X] [Nonempty X] q s hs hs1 hgen hgen0 :
LerayHirschGraded (projMapOf q) (tautEulerOfK K hgen q) s`, and `…DualOf` for `tautEulerDualK`.

## Split with lx-lhK-a (agreed 09-12)
lx-lhK-a: ChartGeneralOf, ChartBundleGenOf, ChartHomeoOf, ChartClassIsoOf (`fibClassOf`, `fibClassOf_ne_zero`),
ChartTautGenOf (`hxi_trivOpenOf`, `rank_le_one_add_tautCardOf`), the K free tuple incl.
`LerayHirschProductOf.hasFreeTuple_cpProd_zeroOf` (unconditional, rank 2) and
`LerayHirschLadderClosedOf.hasFreeTuple_cpProdOf` (consumes `CPn.cupPowE_ne_zeroOf`).
Import DAG: CompactOf(_of_freeTuple) → BootstrapOf → [+ ProductOf] RingClosedOf (`CPn.cupPowE_ne_zeroOf`) →
lx-lhK-a LadderClosedOf → CompactClosedOf (unconditional).

## GREEN
- 0912-101304-26799 (PROBE GREEN, 8848 jobs): `ChernEulerIsoOf` BUILT (+ `ProjectiveSpaceStableOf`), bytes = origin 77c5176d3.
- 0912-102532-50794 (PROBE GREEN, 8989 jobs): ChernEulerEmbedOf, ChernEulerIndexOf, LerayHirschFiniteOf,
  LerayHirschBundleOf, LerayHirschRankOneOf, LerayHirschNegOf — COMPILED; on main 1c07f747f.
- 0912-110215-40113 (lix-q, PROBE FAILED overall): LerayHirschTrivOpenOf (9ca4816cb) and LerayHirschCompactOf
  (68d87ba13) BUILT/COMPILED — `LH.lerayHirschGraded_compactOf_of_freeTuple`, `…DualOf_of_freeTuple`.

## AUTHORED, UNVERIFIED
- ProjectiveSpaceRingBootstrapOf (68d87ba13; fix landing now: `HasFreeTuple` → `LH.HasFreeTuple`):
  `CPn.cupPowE_smulOf`, `rank_plusOne_cpTaut`, `cupPowE_rNotZero_ne_zeroOf_of_freeTuple`,
  `exists_cupPowE_ne_zeroOf_of_freeTuple`, `cupPowE_ne_zeroOf_of_freeTuple`.
- ChernClassesEvenHomogOf (68d87ba13; fix landing now: `simp only [dif_neg h, map_zero]` at 52):
  `LHCast.exists_homog_preimage_lhFunOf`, `LerayHirschDataEvenOf.chern_eq_of_graded` (for lx-bundleP).
- ProjectiveSpaceRingClosedOf (`CPn.cupPowE_ne_zeroOf`) and LerayHirschCompactClosedOf
  (`LH.lerayHirschGraded_compactOf`, `…DualOf`): local + attic copies; import lx-lhK-a's unlanded ProductOf /
  LadderClosedOf, so lxland refuses a normal landing until those exist.

## 12:05 CDT state
- 60eceb761 (landed by me under lane name `lx-lead` — I mistakenly acted as lead after the halt; reported to
  main): RingClosedOf, TowerSumOf, FreeTupleOf, ColSumOf, LadderClosedOf, CompactClosedOf, ChernSplittingOfLHBridge,
  unverified, disk bytes.
- add7fc904: BootstrapOf `LH.HasFreeTuple` + HomogOf `simp only` (NM_BASE after the 3f71a3a50 restore).
- Probe 0912-120155-29904 (lix-q, base add7fc904): HomogOf BUILT/COMPILED; BootstrapOf red on unused `hd`
  (→ `_hd`, landing); CompactClosedOf's closure reaches lx-lhK-a's red `CohomologyChartPeelUniqOf`
  (LadderClosedOf → ColSumOf → FreenessOf → TowerOf → PeelUniqOf; import-only fix landing by lx-lhK-a).
- Holding for my chain tag: lx-splitK (LHBridge probe), lx-stepcK-local (ChernOf + ThomLH), lx-stablyfinite (S3+S4).
- a68c18c37: BootstrapOf `_hd`.  **PROBE GREEN 0912-120910-54878** (lix-q, 9028 jobs): BootstrapOf and
  RingClosedOf BUILT; `CPn.cupPowE_ne_zeroOf` depends on axioms [propext, Classical.choice, Quot.sound].
  Green record covers HomogOf, BundleOf, CompactOf, FiniteOf, NegOf, RankOneOf, TrivOpenOf, BootstrapOf, RingClosedOf.
- lx-lhK-a's PeelUniqOf fix at 577568a3a; its probe 5 compiles TowerOf…FreenessOf.  Sequence agreed: probe 5 →
  lx-stablyfinite S3+S4 (ladder) → my CompactClosedOf probe (restores) → lx-splitK LHBridge, lx-stepcK-local ThomLH.

## DONE 12:20 CDT — target compiled
- **PROBE GREEN 0912-121755-88637** (lix-q, base c7f794109, 9049 jobs): `Built GroupApproximation.CharClass.
  LerayHirschCompactClosedOf (19s)`, sorryAx 0.  `LH.lerayHirschGraded_compactOf` and
  `LH.lerayHirschGraded_compactDualOf` depend on axioms [propext, Classical.choice, Quot.sound] (read in full from the
  remote log; the lines wrap).  Green record covers CompactClosedOf, RingClosedOf, BootstrapOf, HomogOf, CompactOf,
  TrivOpenOf, BundleOf, FiniteOf, NegOf, RankOneOf.
- Closure: lx-lhK-a tower 0912-120703-48079, lx-stablyfinite ladder 0912-120941-56371.
- Notified: lx-splitK (LHBridge), lx-stepcK-local (ChernOf + ThomLH), lx-sliceK (LE/LV), main.
- Not wired into the root (lx-integrator / lead).

## NEXT (one probe when lx-lhK-a's ProductOf lands)  — superseded by DONE above
- land RingClosedOf normally; probe BootstrapOf + HomogOf + RingClosedOf in ONE probe.
- after LadderClosedOf lands unconditional: land + probe CompactClosedOf; message lx-splitK (bridge in their
  `ChernSplittingOfLHBridge`), lx-sliceK, lx-bundleP.

## NEEDS
- lx-lhK-a: `LerayHirschProductOf.hasFreeTuple_cpProd_zeroOf`, unconditional `LerayHirschLadderClosedOf.hasFreeTuple_cpProdOf`.

## SPLIT
- none open (diagonal-cover PlusOne over K is off the critical path; the compact rank-2 route replaces it).

## TRAPS
- Against `∀ (U : Type) [TopologicalSpace U] …`, never `fun U _ d …` (binder shift); use `by intro U _ d …`.
- `rw [dif_neg h]` on `(fun i => if h : … then … else 0) i` fails (beta-redex); `simp only [dif_neg h]` works.
- A file in `namespace CPn` must write `LH.HasFreeTuple` (the def lives in `LH`).
- Transient ENOSPC on the Mac (~11:08 CDT): Edit/Bash failed for a minute; retry, never delete.
