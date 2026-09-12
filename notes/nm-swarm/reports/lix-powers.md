# Lane `lix-powers` (successor of sp-powers), 2026-09-11

Clone: lix-a (shared with lix-tower, lix-oddside-n; rule 20). Owns `Analysis/LIXPowers*`.

## RULINGS
- Sphere hypothesis `IsSphereUnitary` (ContinuousOn off 0, unitary off 0) CONFIRMED by the lead and lix-tower 21:35.
- Ruled pair e₁ := −ε(0,0), e₂ := −ε(0,1) on E n; exponent k ↔ `KGen.bVecK n (k − 1)`.
- `clutch u = FHmat`: off the critical path, not built.

## GREEN
- `Analysis/LIXPowersSphere.lean`: COMPILED, probe 0911-224556-7670 (BUILT line); origin bytes identical (6eba2091b).
- `Analysis/LIXPowersEquator.lean`: COMPILED, probe 0911-225717-66906 (LIXGenericEquator compiled under it).
- `Analysis/LIXPowersEquatorChart.lean`: COMPILED, probe 0911-230906-80909 (`✔ Built`, 106s).

## AUTHORED, UNVERIFIED (landed per rule 18)
- `Analysis/LIXPowersSphere.lean` (2f42d479b): `IsSphereUnitary` (+ mul/star/pow/compRadial), `continuousOn_reparProd`,
  `unit_reparProd_sphere`, `pinchIdentification_angleRepar_sphere` (through `sphereCut`), `isSphereUnitary_normGen`,
  `normGen_wall_sphere`, `exists_homotopy_pow_comp_sphere`, **`exists_homotopy_pow_comp_normGen_sphere`**; the ball
  unitary B = `ballWall e₁ e₂ U y := U (wallRetract y + (1−‖y‖)•(−e₁))` with `wallShift_ne_zero`, `isBallUnitary_ballWall`,
  `ballWall_of_norm_eq_one`, `ballWall_zero`, `normGen_eq_ballWall_mul`.
- `Analysis/LIXPowersEquator.lean` (2f42d479b; `include hn in` fix in attic): `joinPowNeg_neg_neg`, `wallRetract_neg_neg`,
  `eqIdx0`/`eqBasis` orthonormal, `equatorEmb_planeSub`, **`equatorEmb_joinPow`** (= `KGen.psiVec n k ∘ equatorEmb` by
  definition), `isRadialMap_joinPow_equator`, `isSphereUnitary_genSphere`, `genSphere_joinPow`, `ballWall_genSphere_zero`,
  **`exists_homotopy_pow_comp_genSphere`**.
- `Analysis/LIXPowersEquatorChart.lean`: `equatorProj`, `isSuspensionChart_unitVectors` (t = Re x_last),
  `equatorEmb_injective`, `psiUnit` (Σψ_k on S^{2n+1}), `psiUnit_height`, `psiUnit_equator`,
  `clutchMat_comp_joinPow_psiUnit`.

## NEEDS
- Nothing blocking; scope items (1)-(3) are compiled, (4) exists on main (`KGen.normSq_psiVec`), `clutch u = FHmat` is ruled off the path.
- OLD (resolved): - lix-a to finish preparation, then ONE probe: Sphere, Equator, EquatorChart. The Equator closure includes lix-tower's
  `Analysis/LIXGenericEquator` (authored 09-10, never probed); a red there goes to the lead, since lix-tower owns it.

## TRAPS
- `tac <;> rfl` where `tac` leaves exactly one goal is a HARD error under warningAsError ("Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"). Put `rfl` on its own line. It cost two probe rounds, one per file.
- In a section with `variable (hn : 0 < n)`, a theorem whose STATEMENT does not mention `hn` does not get it, even when
  its proof uses it; write `include hn in`.
- `rw [if_neg h]` rewrites only the `ite`s sharing the first match's branches; use `simp only [if_neg h]` for several.
- `rw [pow_succ]` with two `_ ^ (k+1)` in the goal instantiates on whichever it meets first; pin the base.
