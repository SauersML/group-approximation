# Lane ct-two-ended: the two-ended shift remark (tex 1769–1792)

Printed item: `non_mf_groups_exist.tex`, the remark after `cor:dynamic-rank-budget`, tex 1769–1792:
the shift on `X = ℤ ∪ {−∞, +∞}` has LEF units `R_X^× ≅ GL_fin(ℤ, F_2) ⋊ ℤ`, while `GL_3(R_X)` is not MF.

This file is written by ct-two-ended only.

## Landed (all probe-built, #audit clean, wire queued)

| tex | module (SHA) | carriers |
|---|---|---|
| 1769–1773 | `Dynamics.TwoEndedShift` (049c6689a) | `TwoEnded`, `pt`, `posInf`, `negInf`, `isTwoEndedCompactification`, `shift`, `chainRecurrentSet_shift`, `P`, `P_diff_shift_image_P`, `not_isDedekindFiniteMonoid`; closed `printedTwoEndedCoreAndDefect` |
| 1774–1779 | `Algebra.FinitaryGeneralLinear` (f4678fca8) | `FinitaryGL.HasFiniteMatrixSupport`, `SupportedIn`, `GLfin`, `shiftGL`, `shiftAction`, `FinitaryShift` |
| 1779–1780 | `Dynamics.TwoEndedRepresentation` (c6fccaa40) | `rho`, `rho_apply_single_apply`, `rho_injective`, `rho_coeff`, `rho_unit_zpow` |
| 1780–1782 | `Algebra.LaurentMonomialUnits` (6bc66c851) | `exists_single_of_mul_eq_one`, `exists_single_one_of_mul_eq_one_zmodTwo` |
| 1780–1782 | `Dynamics.TwoEndedTailSymbols` (12c78de1b) | `symbolOp`, `symbol`, `symbol_mul`, `exists_tail_pos`, `exists_tail_neg`, `exists_tail_translation_pos`, `exists_tail_translation_neg` |
| 1782–1785 | `Algebra.SupportedCodimension` (164ad2149) | `finrank_quotient_supported_compl`, `card_eq_of_map_supported_compl` |
| 1782–1785 | `Dynamics.TwoEndedTailBalance` (c42cb1e80) | `card_Ioo_eq`, `exists_common_tail_exponent`, `units_map_mul_shiftGL_zpow_mem_GLfin` |
| 1774–1779 | `Dynamics.TwoEndedUnitGroup` (217332545) | `tailExponent`, `unitsToFinitaryShift`, `unitsEquivFinitaryShift`; closed `printedTwoEndedUnitGroup`; `printedTwoEndedUnitsLEFGLThreeNotMF_of_pieces` |
| 1791 | `Dynamics.TwoEndedUnitsLEF` (217332545) | closed `printedTwoEndedUnitsLEF`; `printedTwoEndedUnitsLEFGLThreeNotMF_of_bilateralThree` |

Peer carriers consumed:
- ct-bilateral-cell `Dynamics.TwoEndedMatrixUnits` (0f53d2260): every finitary block times `u^a` is a unit.
- ms-traces-3 `Algebra.FinitaryShiftLEF` (1d55d0846): `FinitaryGL.printedFinitaryShiftLEF`, tex 1786–1791.

## Residual

- Tex 1791–1792, "GL_3(R_X) is not MF". It is assembled in `printedTwoEndedUnitsLEFGLThreeNotMF_of_bilateralThree` over
  `Manuscript.ChainCore.BilateralThree.PrintedBilateralThree` (ct-bilateral-mf; still open on origin at 18375ec10).
  It closes with `printedBilateralThree` once that producer lands.

## Notes

- The symbol is realized through the operator `symbolOp` on `k^{(ℤ)}`. Unfolding a `liftNCRingHom` into
  `AddMonoidAlgebra k ℤ` against the synthesized semiring instances never finished (whnf timeout at 1M heartbeats).
- `x.coeff` on `ClopenCrossedProduct` resolves to the ring hom `ClopenCrossedProduct.coeff`; write
  `SkewMonoidAlgebra.coeff x`.
- ms-core-2's model test `ChainCore.StepSubshiftCoreCalibration.stepSubshift` is the same set as `TwoEnded`.
