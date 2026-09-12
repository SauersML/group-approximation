# Lane leavitt-units: `cor:leavitt-mf-quotient`, first sentence of the proof

Target: `non_mf_groups_exist.tex` line 1307, `\label{cor:leavitt-mf-quotient}`, census row
`7916c8696def` ("The maps x ↦ (t_1x,…,t_dx) and (y_1,…,y_d) ↦ ∑_i s_iy_i are mutually inverse
isomorphisms of right R-modules between R and R^d, so R ≅ M_d(R) and H ≅ GL_d(R).").

## What was missing

The census row was `partial`.  Its carrier
`LeavittMFQuotientSentences.manuscriptSentence_unitsEquivGL` states only the conclusion
`Nonempty (Rˣ ≃* (M_d(R))ˣ)`.  The explicit right-module isomorphism with the printed formulas
existed only at d = 2 and R = L_{F_2}(1,2)
(`UniversalLeavitt.manuscriptSentence_rightModuleSelfSimilarity`), and nothing derived
`R ≅ M_d(R)` from it.

## What this lane adds

Module `GroupApproximation/Manuscript/NonMFSentences/LeavittMFQuotientUnitsGL.lean`
(namespace `GroupApproximation.LeavittMFQuotientUnitsGL`), at every `d` over every field:

* `rightModuleEquiv : R ≃ₗ[Rᵐᵒᵖ] (Fin d → R)`: the printed maps, with the formulas as
  `rightModuleEquiv_apply` and `rightModuleEquiv_symm_apply` (both `rfl`);
* `endEquiv : R ≃+* Module.End Rᵐᵒᵖ (Fin d → R)`: left multiplication
  (`RingEquiv.moduleEndSelfOp`) conjugated along it (`LinearEquiv.conjRingEquiv`);
  `endEquiv_apply_eq_mulVec` shows that `endEquiv x` is left multiplication by the matrix
  `ringEquivMatrix x = (t_ixs_j)_{ij}`;
* `endMatrixEquiv : End_R(R^d) ≃+* M_d(R)`, with `endMatrixEquiv_apply` (the matrix on the
  standard basis);
* `unitsEquivGLPrinted : Rˣ ≃* Matrix.GeneralLinearGroup (Fin d) R`, which agrees with the
  consumed `LeavittMFQuotientGeneral.unitsEquivGL` (`unitsEquivGLPrinted_val_eq_unitsEquivGL`);
* closed endpoint `PrintedLeavittUnitsRightModuleIso` / `printedLeavittUnitsRightModuleIso`
  over every countable field and every d ≥ 2 (`#audit_closed_axioms` passed in the GREEN
  probe).

No literature input.

## Sweep of the environment and its proof (tex 1297–1323)

| key | line | status | carrier |
| --- | --- | --- | --- |
| `dcf6fa4be4de` | 1298 | definition (carriers now named) | `AryLeavitt.AryLeavittAlgebra`, `genS`, `genT`, endpoint binders |
| `6aef426dfc7a` | 1298 | formalized | `LeavittKOneFormulaSentences.PrintedLeavittMFQuotientFull` |
| `7916c8696def` | 1307 | **partial → formalized** (this lane) | `LeavittMFQuotientUnitsGL.PrintedLeavittUnitsRightModuleIso` |
| `3c68c15758e8` | 1307 | formalized | (census) |
| `4321530b3fec` | 1307 | formalized | (census, leavitt-k1) |
| `f6962254d259` | 1307 | formalized | (census) |
| `LINE:1312`, `LINE:1315` | 1312, 1315 | formalized | (leavitt-ge) |
| `6d3ca647302e` | 1320 | formalized | (census, leavitt-k1) |

Every sentence of the environment and its proof is now `formalized` or a naming `definition`
row with carriers.  The environment is closed.

## Status

* LANDED `4f629158e` (orphan, not wired).  It compiled unchanged: probe `0912-102543-53051`
  GREEN on base `552014bcf` (BUILT and COMPILED
  `GroupApproximation.Manuscript.NonMFSentences.LeavittMFQuotientUnitsGL`), md5 `8c482570…`
  identical on origin, so the green landing reported NOTHING TO LAND.
* Census rows: `$NM/rows/leavitt-units.tsv` → `metadata/nm-census-rows/leavitt-units.tsv`
  (`7916c8696def` formalized, `dcf6fa4be4de` definition with carriers).
* Report first landed `92e9f4497`.
