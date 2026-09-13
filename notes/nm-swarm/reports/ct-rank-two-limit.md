# Lane ct-rank-two-limit: the rank-two limitation remark (tex 1794–1807)

Target: `non_mf_groups_exist.tex`, sec:chain-core, the remark after `cor:dynamic-rank-budget`
("There is also a limitation of the compression method at rank two ..."), every sentence, closed.

## GHW Theorem 4 check

`GHW.printedGHWTheoremFour : PrintedGHWTheoremFour` (Kazhdan/GHWTheoremFourClosed, closed at 66417a372)
covers every field `K` and every countable subgroup of `GL_2(K)`.  `GL_2(k[z,z^{-1}])` embeds in
`GL_2(Frac k[z,z^{-1}])`, so the printed consumption has no gap.

## Already on main (consumed, not rebuilt)

- `JacobsonRankTwo.finite_image_and_finite_of_kazhdan` (Manuscript/OneSidedMFRadical/JacobsonRankTwoInert):
  a hom with locally finite kernel into a group whose countable subgroups are Haagerup kills
  nothing infinite: every Kazhdan subgroup is finite.  This is the printed deduction
  "Haagerup + (T) ⇒ finite image; finite-index f.g. locally finite kernel ⇒ finite".
- `printedDefect_eq_bot_of_finite` (DefectSaturation): finite subgroups have trivial printed defect.
- `ClopenCrossedProduct.restrict`, `restrictHomeo` (Dynamics/ClopenCrossedProductComap): core restriction.

## Modules (this lane)

| module | content | status |
|---|---|---|
| `Kazhdan/HaagerupFiniteProduct` | `hasHaagerupProperty_of_injective_pi`, `hasHaagerupProperty_of_injective_pi_glTwo` (GHW at finitely many `GL_2` over fields) | LANDED 8509c9a55 |
| `Algebra/LocallyFiniteCongruenceKernel` | `HasLocallyFiniteKernel ρ`; `hasLocallyFiniteKernel_of_isLocallyMatricialIn`; `glMap n ρ` (noncommutative rings); `isLocallyFiniteGroup_ker_glMap`, `isLocallyFiniteGroup_ker_unitsMap` | LANDED 70317e581 |
| `Dynamics/RankTwoKazhdanLimitStatements` | step Props and printed endpoints (below) | LANDED 70317e581 |
| `Dynamics/RankTwoKazhdanLimitAssembly` | `printedFixedCoreGLTwoKazhdanFinite_of_steps`, `printedPeriodTwoCoreUnitsKazhdanFinite_of_steps`, `printedRankTwoCompressionDefectsTrivial_of_steps` | LANDED 70317e581 |
| `Dynamics/ClopenCrossedProductLaurentEval` | `evalLaurent` (fixed points into `k[z,z^{-1}]`), `evalPair` (period ≤ 2 into `M_2(k[z,z^{-1}])`), `coeff_evalLaurent`, `coeff_evalPair_row` | probing |
| `Dynamics/RankTwoCoreImageHaagerup` | `fiberSubring`; `fixedCoreImageHaagerup`, `periodTwoCoreUnitImageHaagerup`; endpoints `*_of_kernel` | probing |

Printed endpoints (namespace `GroupApproximation.ChainCore.RankTwoLimit`):
`PrintedFixedCoreGLTwoKazhdanFinite` (tex 1795–1796), `PrintedPeriodTwoCoreUnitsKazhdanFinite` (tex 1802–1803),
`PrintedRankTwoCompressionDefectsTrivial` (tex 1801–1802).  The kernel lemmas serve any lane that needs local
finiteness of `K_n(I)` over a finite field (`lem:involution-localization` states it for `K_1(I)`; `thm:core-mf-radical`
for `n ≥ 2` over `F_2`).

## Residual Props

- `CoreRestrictionLocallyFiniteKernelStatement`: for compact metric totally disconnected `X`, `T`, finite field `k`,
  `HasLocallyFiniteKernel (ClopenCrossedProduct.restrict T k (image_chainRecurrentSet T))`.
  Producer: lem:transient-matrices (chain-matricial, `isLocallyMatricialIn_transientIdeal`), via
  `hasLocallyFiniteKernel_of_isLocallyMatricialIn` in this lane's module.
- `FixedCoreImageHaagerupStatement`, `PeriodTwoCoreUnitImageHaagerupStatement`: this lane (in progress).

## Progress log

- 09-13 16:45: plan; GHW check passed; four modules probing.
