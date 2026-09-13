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

## Residual Props (all mine)

1. `ReturnSectionStatement` — in progress (`Dynamics/ReturnSection.lean`: separated clopen cover, recursion
   `sectionStep`, clopen, separation, covering, gaps via the middle point `T^r x`).
2. `FirstReturnStatement` — next (`Dynamics/FirstReturnMap.lean`).
3. `ReturnTowerUnitsStatement` — the tower partition in `R_X` (`Dynamics/ReturnTowerCrossedProduct.lean`).
4. `ReturnRingCrossedProductStatement` — splitting partial shifts along returns (`Dynamics/ReturnRingCrossedProduct.lean`).
5. Printed-sentence assembly and census rows after 1–4 close.

## Progress log

- 09-13 16:37: ReturnTowerUnits GREEN (first probe), LANDED 28cd138ca.
- 09-13 16:48: ReturnTowerStatements GREEN after an import fix.
