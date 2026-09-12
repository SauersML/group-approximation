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

## AUTHORED, UNVERIFIED
- none

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
