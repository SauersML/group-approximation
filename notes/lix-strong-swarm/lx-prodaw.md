# lx-prodaw — `CharClass/OddPProductAW.lean` (item 3 of lx-cartan-b's lemma list)

Clone spare2.  Owns `CharClass/OddPProductAW*`.  Interface: lx-cartan-b's spellings (message 09-12).

## AUTHORED, UNVERIFIED (landed per rule 5')
- 2162aa664 part 1: `awFrontHom`, `awBackHom`, `awFront`, `awBack` (cast-free `restrictSimplex` faces, `Fin (n+1)`
  cut), `awFront_natural`, `awBack_natural`, bridges `awFront_eq_topPow`, `awBack_eq_topPow`, `vtx_id_self`;
  `gCupFun`, `tagEvalG_gCupFun`, `tagEvalG_gCupFun_range`, `gCupFun_of_ne`, `gCupFun_piSingle`, `gSign`,
  `tagEvalG_gSign`, `lc_tagEvalG_tagBd`, `tagEvalG_gCoboundary_gCupFun`, `gCoboundary_gCupFun` (Leibniz via
  `TopPow.binary_aw` with the bilinear map `(LinearMap.mul K K).compl₁₂ …`); `tupInterleave`, `awSlot`,
  `tupInterleave_even/_odd/_eta`, `prod_awSlot`, `sum_awSlot`, `awCuts`, `awTupOf`, `sum_awTupOf`, `awTupAll`,
  `awTupAll_single`, `tupEvalAll_awTupAll_single`, `tupEvalAll_awTupAll`.
- e814dde90 part 2: `awFinExt`, `sum_Iio_eq_sum_range_awFinExt`, `sum_range_two_mul`, `prefix_awSlot_even/_odd`,
  `tupEvalAll_update_eq_add_smul`, `tagEvalG_gCupFun_gSign_of_homog`, `tagEvalG_gCoboundary_gCupFun_of_homog`,
  `gCupFun_update_even/_odd`, `tupEvalAll_awTupAll'`, **`tupDAll_awTupAll`**.
- part 3 (landing): `rot_sign_arith`, `tupRot_iterate_two_awTupOf`, `awTupOf_rotExp`, **`awTupAll_tupTAll`**,
  `tupPush_awTupOf`, **`tupAllMap_awTupAll`**, **`awTup`**, **`tupIncl_comp_awTup`**, **`awTup_tupD`**,
  **`awTup_tupT`**, **`awTup_tupMap`**, **`awTup_diagPt`**.

- 2968d8530 part 3 (above).  Split (landing): `awTup_diagPt` moved to NEW `CharClass/OddPProductAWDiag.lean`
  (imports OddPProductAW + OddPDiagonalSrc); OddPProductAW no longer imports OddPDiagonalSrc.

## GREEN
(none yet; never compiled)

## PROBES
- 0912-115949-21053 (spare2, acn112 slot 0, base 142e9d35b): PROBE FAILED before reaching OddPProductAW —
  red IMPORTS on main: `OddPProductEval` (instance synthesis 68:36, 71:39, 82:17, 96:74; unsolved 99:4; likely
  missing classical DecidableEq on TagSimp/TupAll) → messaged lx-prodeval; `OddPTopPowerAW` (deprecated
  `Fin.lt_iff_val_lt_val`, `Fin.coe_castSucc`; omega 127:6; rw 157:6) → messaged lx-toppower; `OddPDiagonalAug`
  (isDefEq timeout 262:0, lx-diag) → removed from my closure by the split.  Re-probe once both owners land fixes.

## NEEDS
- none.  Imports on main: OddPProductEval (2590c0d3b), OddPTopPowerAWChain (249cfba63), OddPEvalMultilinear,
  OddPDiagonalSrc.

## RISKS AT FIRST COMPILE (blind authoring)
- `Pi.single_eq_of_ne` argument order at the pin; `simp only [... ↓reduceIte]` shapes in `tupInterleave_even/_odd`;
  the `simp only … at key` normal form in `tagEvalG_gCoboundary_gCupFun` before `exact key.symm`; `rw` closing by
  reducible `rfl` in `awFront_eq_topPow` / `tagEvalG_gCupFun_range`; `Finset.sum_equiv` reindexing with a `let`
  equivalence in `awTupAll_tupTAll`.

## TRAPS
- git grep without `-P`/`-F`: `\b` silently matches nothing (a Mathlib name search printed empty).
- Local disk at 100% (418 MiB free, 09-12 ~11:00): zsh "no space left on device"; reported to main.
