# Lane ct-return-tower: the tower half of cor:dynamic-rank-budget

Tex: `non_mf_groups_exist.tex` (origin/main, 2507 lines), proof of `cor:dynamic-rank-budget`, lines 1707–1741:
the section construction, first-return cells and homeomorphism, `P_C ≅ LC(C,k) ⋊_{S_C} ℤ`, the tower `D_i, a_i, b_i`,
the unital corner, `Φ`, unitization and block elementary flattening.  Consumer: ct-rank-budget (tex 1743–1766).

## Interface names (consume these)

Module `GroupApproximation.Algebra.ReturnTowerUnits` (namespace `GroupApproximation.ChainCore`), LANDED 28cd138ca, probe GREEN:

| printed object | declaration |
|---|---|
| a tower `(p, a_i, b_i)` with `b_i a_j = 0` (`i ≠ j`), `∑ a_i b_i = 1`, `b_i a_i = p` for `i < r` | `ReturnTowerUnits R N r` (fields `p a b le isIdempotentElem_p a_mul_p p_mul_b b_mul_a_of_ne sum_a_mul_b b_mul_a_of_lt`) |
| `P_C = p_C R p_C` | `τ.Base` (= `MFQuotientUnits.Corner R τ.p _`) |
| `x ↦ (b_i x a_j)_{ij}` | `τ.toMatrix : R →ₙ+* Matrix (Fin N) (Fin N) τ.Base`, `toMatrix_apply` |
| `R` a unital corner of `M_N(P_C)` | `τ.cornerEquiv : R ≃+* Corner (Matrix ..) (τ.toMatrix 1) _`; `τ.isDedekindFiniteMonoid` (DF of `M_N(P_C)` ⇒ DF of `R`) |
| `Φ(A) = ∑_{i,j<r} a_i A_ij b_j`, injective | `τ.phi : Matrix (Fin r) (Fin r) τ.Base →ₙ+* R`, `phi_apply`, `phi_injective`, `b_mul_phi_mul_a`, `phi_one` |
| unitization `GL_n(M_r(P_C)) → GL_n(R)` | `τ.unitize n` (monoid hom), `τ.unitizeGL n`, `unitize_apply` (`diagonal (1 - Φ 1) + M.map Φ`), `unitizeGL_injective` |
| after flattening `GL_{n×r}(P_C) → GL_n(R)` | `τ.flatUnitizeGL n`, `flatUnitizeGL_injective` |
| `EL` lands in `EL_n(R)` (`n ≥ 2`) | `unitizeGL_elementaryUnit`, `map_elementaryGroup_le`, `map_flat_elementaryGroup_le [Nontrivial n]` |

Module `GroupApproximation.Dynamics.ReturnTowerStatements`, probe GREEN 0913-164817-8963 (landing with this report):

| printed object | declaration |
|---|---|
| no points of period `< r` (r = 2: no fixed points; r = 3: no periods one or two) | `NoShortPeriods T r` |
| `C` clopen, separated from first `r-1` translates, `X = ⋃_{|j|<r} T^j C` | `IsReturnSection T r C` (fields `isClopen`, `disjoint_image`, `exists_mem_image`) |
| return gaps in `[r, 2r-1]` | `ReturnGapsIn T C r (2*r-1)` |
| first return time | `returnTime T C x` |
| section construction (tex 1709–1719) | `ReturnSectionStatement` |
| return times, cells `C_h` clopen, `S_C` homeomorphism (tex 1721–1722) | `FirstReturnStatement` |
| the tower in `R_X` is a `ReturnTowerUnits` system over `p_C = 1_C`, `a_i = u^i 1_{D_i}`, `b_i = 1_{D_i} u^{-i}` (tex 1727–1731) | `ReturnTowerUnitsStatement` |
| `P_C ≅ LC(C,k) ⋊_{S_C} ℤ`, coefficients ↦ extension by zero, `u ↦ v = ∑_h u^h 1_{C_h}` (tex 1723–1726) | `ReturnRingCrossedProductStatement` |

## Closed endpoints

| Prop | closed declaration | module | SHA |
|---|---|---|---|
| `ReturnSectionStatement` (tex 1709–1719) | `returnSectionStatement_holds` | `Dynamics/ReturnSection` | e4a681074 |
| `FirstReturnStatement` (tex 1721–1722) | `firstReturnStatement_holds` | `Dynamics/FirstReturnMap` | e4a681074 |

More consumable names:
- `Dynamics/ReturnSection`: `exists_separated_clopen_cover`, `nearOrbit`, `sectionStep` (the printed recursion),
  `exists_isReturnSection`, `IsReturnSection.exists_return` (every point visits `C` within `2r-1` steps),
  `returnTime_spec`, `returnTime_min`, `returnTime_le_of_mem`, `returnTime_eq_of`, `le_returnTime`, `returnTime_le`,
  `IsReturnSection.returnGapsIn`, `IsReturnSection.eq_univ_of_one`, `isReturnSection_univ_one`.
- `Dynamics/FirstReturnMap`: `returnCell T C h`, `returnCell_eq`, `isClopen_returnCell`, `IsReturnSection.inv`,
  `firstReturnFun`, `firstReturnHomeomorph hC : C ≃ₜ C` (`firstReturnHomeomorph_apply`: `S_C x = T^{h(x)} x`).

| `ReturnTowerUnitsStatement` (tex 1727–1734) | `returnTowerUnitsStatement_holds` | `Dynamics/ReturnTowerCrossedProduct` | 7b0a3343c |

- `Dynamics/ReturnTowerCrossedProduct`: `towerLevel T C i` (= `D_i`), `isClopen_towerLevel`, `towerLevel_of_lt`
  (`D_i = C` for `i < r`), `exists_mem_image_towerLevel` / `eq_of_mem_image_towerLevel` (the tower partition),
  `unitPow T k j` (`u^j`), `unitPow_mul`, `unitPow_mul_coeff`, `comap_zpow_neg_charFn`, `towerA`, `towerB`,
  `returnTowerUnits k hC hr : ReturnTowerUnits R_X (2r-1) r` with rfl lemmas `returnTowerUnits_p/_a/_b`.

| `ReturnRingCrossedProductStatement` (tex 1723–1726) | `returnRingCrossedProductStatement_holds` (ms-core-1; surjectivity from this lane's `surjective_of_generators`) | `Dynamics/ReturnRingCrossedProduct` | 69cfc53ff |

All four tower Props of cor:dynamic-rank-budget are closed.

## `ReturnRingCrossedProductStatement` (tex 1723–1726), split with ms-core-1 — CLOSED 69cfc53ff

- Mine, LANDED: `Dynamics/ReturnCells` cc54707b9 and `Dynamics/ReturnRingUnit` 71084d8c5 (both probe GREEN).  Contents: `Dynamics/ReturnCells` (`image_returnCell`: `T^h C_h = returnCell T⁻¹ C h`; `returnCell_eq_empty_of_le`;
  `disjoint_returnCell`; `sum_indicator_returnCell`; `clopenExtendByZero` with `_mul/_add/_zero/_one/_injective/_eq_of/
  _restrict`; `exists_separated_clopen_cover_abs`, the printed `0 < |j| < r` spelling) and `Dynamics/ReturnRingUnit`
  (`returnP`, `cellCoeff`, `backCellCoeff`, `returnV` = printed `v`, `returnW`, `returnUnit k hC : (ReturnCorner k hC)ˣ`,
  covariance `returnV_mul_coeff_extend`).
- Mine, LANDED 2acee7950 (probe 0913-181404-34653 GREEN): `Dynamics/ReturnCornerGeneration`, the surjective half
  (tex 1724–1726, "split any partial shift with endpoints in C according to its successive returns"):
  `returnMonomial k hC n` (= p_C u^n p_C), `returnMonomial_natCast_eq` (n > 0: ∑_{0<h≤n} 1_{C'_h} v p_C u^{n-h} p_C),
  `returnMonomial_neg_natCast_eq` (n < 0: forward cells and w), `backCellCoeff_mul_unitPow_mul_returnP_of_lt`,
  `cellCoeff_mul_unitPow_neg_mul_returnP_of_lt` (cells with h > |n| contribute zero), `returnCornerGenerators`,
  `mem_closure_returnCornerGenerators` (P_C = subring generated by extended coefficients, v, w), and the criterion
  `surjective_of_generators k hC φ hcoeff hv hw : Function.Surjective φ`.
- ms-core-1 (sent by main): `Algebra/ZCrossedProductLift` (8c0e01a29), `Algebra/ZCrossedProductDegree`,
  `Dynamics/ReturnRingLift` (`returnRingHom`), `Dynamics/ReturnRingInjective`, and the endpoint
  `Dynamics/ReturnRingCrossedProduct` (`returnRingHom_surjective` via `surjective_of_generators`, `returnRingEquiv`,
  closed `returnRingCrossedProductStatement_holds`).

## Census rows

`metadata/nm-census-rows/ct-return-tower.tsv` LANDED 988ae81b2: tex 1710, 1716, 1717, 1719, 1721, 1722, 1727, 1731, 1732,
1734, 1739, 1740.  Pending: 1709 (after ReturnCells lands), 1723 and 1726 (after the ring iso).

## Progress log

- 09-13 16:37: ReturnTowerUnits GREEN (first probe), LANDED 28cd138ca.
- 09-13 16:48: ReturnTowerStatements GREEN after an import fix, LANDED 4d2084188.
- 09-13 17:06: ReturnSection and FirstReturnMap GREEN, LANDED e4a681074; both Props closed.
