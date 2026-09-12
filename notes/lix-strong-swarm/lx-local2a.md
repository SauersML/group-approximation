# lx-local2a — rank-n comparison homotopy and legs of the local square (p = 2 geometry, coefficient-free)

Clone lix-b (shared with lx-local2b).  Owns `CharClass/LIXKGenLocalHomotopy*`, `LIXKGenLocalLegs*`, and existing non-`Of`
`LIXKGen*` geometry except `LIXKGenLocal*`.

## Interface agreements (2026-09-12)
- With lx-local2b: there is no `LIXKGenLocalLegs` file.  The coefficient-free leg maps live in `LIXKGenLocalHomotopy`.  All
  relative-pullback identities, the homotopy cut, the chains and the nonvanishing belong to lx-local2b over `ZMod 2`
  (`LIXKGenLocalSquare`, `LIXKGenLocalNonzero`) and to lx-stepcK-local over a field `K` (`LIXKGenOfLocalSquare`).
- Route: no excisions.  The left leg lands in `(lixKTrivBall, val⁻¹' (lixKZeroSet)ᶜ)`, the pair of `LIXKRelMV.restrictTo`.

## GREEN
- `GroupApproximation/CharClass/LIXKGenLocalHomotopy.lean`
  - landed at fb1085202 (first as unverified); these bytes are the ones probed
  - probe 0912-102831-69207, base fb1085202, SLURM acn02, 8 cpus
  - `BUILT GroupApproximation.CharClass.LIXKGenLocalHomotopy`, `Build completed successfully (8938 jobs)`, PROBE GREEN
  - evidence `lanes/lx-local2a.green.0912-102831-69207`
  - `#audit_axioms`: `[propext, Classical.choice, Quot.sound]`

Declarations (namespace `GroupApproximation.CharClass.KGen`, binders `(n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) {G} (hGc)
(hGu) [(hGe)]`):
- **Chart point:** `lixKBC_apply` (@[simp] rfl), `lixKHsqBall_subset_baseChart_source`, `lixKQ`, `lixKQ_mem`, `continuous_lixKQ`,
  `lixKProductChart_lixKQ`.
- **Continuity:** `continuous_lixKTau`, `continuous_lixKEtaLin_pair`, `continuous_lixKHomotopySmul`, `lixKHomotopySmul_mem`,
  `continuous_lixKHomotopyBase`.
- **Homotopy:** `lixKHomotopyVec`, `lixKHomotopyVec_mem`, `lixKHomotopyFun : C(↥lixI × ↥(lixKU …), Bundle.Total (lixBundle n G hGc hGu))`,
  `lixKHomotopyVec_ne_zero`, `lixKHomotopy_mapsTo`.
- **Fibre and ends:** `lixKFibre_mem`, `lixKFibreMap`, `lixKFibreMap_mapsTo`.
  - `lixKHomotopy_at_one : … = lixKSectionTotal n k hGc hGu hGe (lixKBC n k dd i (lixKQ … v))`
  - `lixKHomotopy_at_zero : … = lixKFibreMap … (lixKGLin n k i hGc hGu v)`
- **Left leg:** `lixKChartPt_mem`, `continuous_lixKChartPtFun`, `lixKChartPt`, `lixKGLmap`, `lixKGL_mapsTo`, `lixKGLmap_apply`.
  - `lixKChartPt_mapsTo`: off the origin, the chart point misses every zero.  It misses `z_i` by injectivity of `lixKBC` on its source, and every other zero because the neighbourhood holds none.
- **Right leg:** `lixKIncF`, `lixKIncF_mapsTo`, `lixKTrivInv`, `lixKInclOn`, `lixKTrivInv_mapsTo`, `lixKInclOn_mapsTo`, `lixKGRmap`,
  `lixKGRmap'`, `lixKFarMap`, `lixKSplit_mapsTo`, `lixKGFibre_mapsTo`, `lixKGR_mapsTo`, `lixKGR'_mapsTo`, `lixKFar_mapsTo`,
  `lixKTrivInv_apply`, `lixKGRmap_eq`, `lixKFarMap_apply`.
- **Ends as legs:** `lixKHomotopy_end_one`, `lixKHomotopy_end_zero`.

## AUTHORED, UNVERIFIED (task 2, 09-12: lx-lhK-a's SPLIT S1 and S2)
- `GroupApproximation/CharClass/LerayHirschTowerSumOf.lean` (S1, namespace `LH`).
  - Over `{K} [CommRing K]`: `lhTerm_index_congrOf`, `sum_cup_rightOf`, `lhTerm_succ_rightOf`.
  - `peelTower_eq_sumOf K U d h m a k : KnCP.peelTowerOf K U d h m a k = ∑ i : Fin (k+1), lhTerm (KnCP.cpPrU U d)
    (pull (KnCP.cpPrCP U d) 2 h) (m + 2*k) (k - i) (cohCast _ (a i))`.
  - Imports `LerayHirschTowerSum`, `CohomologyChartTowerOf`.
  - Proofs are the F₂ file verbatim with `Hmod2 → Hmod K`, `cpGen (d+1) hd → h`, `peelTower U d hd → peelTowerOf K U d h`.
- `GroupApproximation/CharClass/LerayHirschFreeTupleOf.lean` (S2, namespace `LH`).
  - This is lx-lhK-a's draft, adopted; lx-lhK-a no longer edits it.
  - Declarations: `sum_lhTerm_range_leOf`, `towerCoeffOf`, `towerCoeff_of_leOf`, `towerCoeff_of_gtOf`, `towerSumFunOf`,
    `towerSumFun_eq_zero_of_gtOf`, `lhTerm_eq_zero_of_rankOf`, `towerSumFun_eq_zero_of_rankOf`, `tower_index_congrOf`,
    `towerCoeff_revOf`, `peelTower_eq_range_sumOf`, `sum_towerSumFun_range_leOf`.
  - `exists_freeTupleOf K U d hring h h0 n z`.
  - Added: the AxiomGuard import and three `#audit_axioms`.
- LANDED (unverified): both files are on origin through the lead's wave 60eceb761 (11:50), with blobs = disk (`9b99e1d563f6`, `50a6e795b8fd`).
  Attic copies went up earlier at 8db017184, while the tower chain was absent from origin after the becc912bd restore.
- lx-lhK-a's tower chain is on origin at 3c6fbec99.  Its bytes equal disk, and `peelTowerOf`, `exists_peelTowerOf`,
  `cupPowE_pull_eq_zeroOf` and `CPRingOf` match the spellings S1/S2 use.
- The group probe (S1+S2, one probe on lix-b) is HELD until lx-lhK-a's probe 5 ends.  Probe 4 (0912-113840-34864) was red on
  an import-only defect in `CohomologyChartPeelUniqOf` below the tower chain.  Probing first would compile the same chain
  twice and inherit the red.

## SPLIT (independent sub-tasks for helpers)
- None open in this lane.  The coefficient-free geometry of the rank-n local square is complete and green, and
  `LIXKGenLocalLegs` is intentionally not a separate file: its maps are in `LIXKGenLocalHomotopy`.
- Adjacent, outside this lane (prefix `LIXKStepCExponent*` belongs to lx-local2b): the rank-two `KLocalNonzero k hGc hGu hGe`
  (`CharClass/LIXKStepCExponent.lean`) has no producer on main.  It is off the critical path: `LemmaTwoHoldsAtPowers` uses the
  rank-n `KZeroLocalData`, which lx-local2b's `LIXKGenLocalNonzero` produces.

## NEEDS
- none

## Consumers on main (checked at bb216c03d)
- lx-local2b: `LIXKGenLocalSquare`, `LIXKGenLocalNonzero`, landed unverified at d8c038bcf.
- lx-stepcK-local: `LIXKGenOfLocalSquare`, d3fefdbc6.
- Every `lixK*` identifier those files use is declared on main.

## TRAPS
- `KGen.lixKI` is already taken in `LIXKGenBundle` (restriction to the complement of a zero).  The homotopy's parameter interval is
  the rank-two `CharClass.lixI`, with `contractibleSpace_lixI`.
- The probe's msi hop is slow.  The overlay and job uploads took ~12 min before dispatch, while the build itself was short.  The
  pending md5 file in `lanes/` shows a probe is still in flight: poll the output file inside the turn instead of assuming it died.
