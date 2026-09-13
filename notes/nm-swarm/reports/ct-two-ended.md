# Lane ct-two-ended: the two-ended shift remark (tex 1769–1792)

Printed item: `non_mf_groups_exist.tex`, the remark after `cor:dynamic-rank-budget`, tex 1769–1792
(origin 049c6689a numbering): the shift on `X = ℤ ∪ {−∞, +∞}` has LEF units
`R_X^× ≅ GL_fin(ℤ, F_2) ⋊ ℤ`, while `GL_3(R_X)` is not MF.

This file is written by ct-two-ended only.

## Landed

- `GroupApproximation.Dynamics.TwoEndedShift` (049c6689a; probe 0913-173838-9003 BUILT), tex 1769–1773,
  namespace `GroupApproximation.TwoEndedShift`:
  - `TwoEnded` (monotone maps `ℤ → Bool`), `pt j`, `posInf`, `negInf`;
    `isTwoEndedCompactification : IsTwoEndedCompactification TwoEnded pt posInf negInf`;
    instances `CompactSpace`, `SecondCountableTopology`, `MetrizableSpace`
  - `shift : TwoEnded ≃ₜ TwoEnded`, `shift_pt`, `shift_posInf`, `shift_negInf`
  - `chainRecurrentSet_shift : Dynamics.chainRecurrentSet shift = {negInf, posInf}`
  - `P`, `isClopen_P`, `P_eq`, `shift_image_P_subset`, `P_diff_shift_image_P : P \ shift '' P = {pt 0}`
  - `not_isDedekindFiniteMonoid : ¬ IsDedekindFiniteMonoid (ClopenCrossedProduct shift (ZMod 2))`
  - closed endpoint `printedTwoEndedCoreAndDefect : PrintedTwoEndedCoreAndDefect` (`#audit_closed_axioms`)
  - wire queued.

## In flight (text copies under attic/inflight/ct-two-ended/)

- `GroupApproximation.Algebra.FinitaryGeneralLinear` (tex 1774–1779), namespace `GroupApproximation.FinitaryGL`:
  `HasFiniteMatrixSupport`, `SupportedIn`, `hasFiniteMatrixSupport_iff`, `supportedIn_inv`, `GLfin k`,
  `shiftGL k`, `shiftGL_zpow_single`, `shiftGL_zpow_apply`, `conj_mem_GLfin`,
  `shiftAction k : Multiplicative ℤ →* MulAut (GLfin k)`, `FinitaryShift k := GLfin k ⋊[shiftAction k] Multiplicative ℤ`.
- `GroupApproximation.Dynamics.TwoEndedRepresentation` (tex 1779–1780): `diag k f`, `diagHom k`, `coeffHom k`,
  `shiftHom k`, `rho k : ClopenCrossedProduct shift k →+* Module.End k (ℤ →₀ k)`,
  `rho_apply_single_apply : rho k x (single i c) l = (of.symm (x.coeff (ofAdd (l − i)))) (pt l) * c`,
  `rho_injective`, `rho_coeff`, `rho_unit_zpow`.

## Residual steps (along the printed route)

1. Laurent symbols (tex 1780–1782): a unit's symbols at the fixed endpoints are `z^{a_−}`, `z^{a_+}`, and `ρ(x)`
   translates the far tails by them.
2. Codimension count (tex 1782–1785): the tail span `k^{(≤−N) ∪ (≥N)}` has codimension `2N − 1`, its image
   `2N − 1 + a_+ − a_−`, so `a_+ = a_−`; then `ρ(x) σ^{−a} ∈ GL_fin`.
3. Surjectivity: every finitary block and every `u^a` is a unit (matrix units `ρ(1_{\{r\}} u^{r−c})`).
4. `R_X^× ≃* FinitaryGL.FinitaryShift (ZMod 2)` (tex 1774–1779).
5. "R_X^× is LEF although GL_3(R_X) is not MF" (tex 1791–1792): LEF from ms-traces-3's
   `FinitaryGL.PrintedFinitaryShiftLEF` (module `Algebra/FinitaryShiftLEF`, tex 1786–1791); not MF from
   ct-bilateral-mf's `PrintedBilateralThree` (Manuscript/ChainCore/BilateralThreeStatement) at `n = 3` with
   `not_isDedekindFiniteMonoid`.

## Notes

- ms-core-2's model test `ChainCore.StepSubshiftCoreCalibration.stepSubshift` is the same set as `TwoEnded`
  (configurations that stay `true`); it is a calibration, not a carrier, so there is no conflict.
