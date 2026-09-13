# Lane ct-rank-budget: cor:dynamic-rank-budget (tex 1696–1767) and the Introduction aperiodic sentence

Snapshot: origin/main (09-13; tex unchanged since 73a84cd9c).  Roster: ct lead session (not the every-line
coordinator).  This file is written by ct-rank-budget only.

## Printed items owned

- cor:dynamic-rank-budget statement (tex 1696–1705).
- Its proof, tex 1743–1766: the induced core `C ∩ Y`; `J = p_C I p_C`; the `F_2` radical equality; the transfer
  over other finite fields; the positive implications.
- Introduction (tex 254–259): "If T is aperiodic, the same conclusion holds already for the unit group and for every
  elementary rank n ≥ 2."

## Modules

1. `GroupApproximation/Manuscript/OneSidedMFRadical/MFRadicalTransport.lean` — LANDED fbd3fae3c (probe
   0913-163109-42427 GREEN), wiring queued.  Namespace `GroupApproximation.MFRadicalTransport`:
   `map_mfHomKernel_le`, `mem_mfHomKernel_of_conj_mem`, `le_mfHomKernel_of_conj_mem_map`, `mfHomKernel_le_ker`,
   `mfHomKernel_eq_bot_of_isOperatorMF`, `mfHomKernel_eq_ker_of_le`, `mfHomKernel_eq_ker_of_conj_into_embedded`,
   `quotientMFRadicalEquivRange`, `isLEF_range`, `isOperatorMF_range_of_isLEF`, `not_isOperatorMF_of_injective_of_mem`,
   `isOperatorMF_iff_isLEF_and_isLEF_iff_of_pieces`, `isDedekindFiniteMonoid_of_injective_nonUnitalRingHom`
   (+`_matrix`), `not_isDedekindFiniteMonoid_of_tower_corner`.  Generic; chain-radical may consume
   `mfHomKernel_le_ker` / `mfHomKernel_eq_ker_of_le` instead of re-proving them.
2. `GroupApproximation/Manuscript/NonMFSentences/DynamicRankBudget.lean` — LANDED a2cb17f58 (probe
   0913-165527-31471 GREEN), wiring queued.  Namespace
   `GroupApproximation.ChainCore.DynamicRankBudget`:
   - core restriction and kernels: `image_core`, `coreRestrict`, `glCoreRestrict`/`glCoreKernel`,
     `elCoreRestrict`/`elCoreKernel`, `unitCoreRestrict`/`unitCoreKernel` (over `ClopenCrossedProduct.restrict` and
     `Dynamics.chainRecurrentSet`);
   - `def PrintedDynamicRankBudget : Prop` (tex 1696–1705 as printed), `def PrintedIntroductionAperiodicSentence`;
   - `printedDynamicRankBudget_of_pieces` (the printed proof over the pieces below),
     `printedIntroductionAperiodicSentence_of_budget`.
3. `GroupApproximation/Manuscript/NonMFSentences/DynamicRankBudgetTorsionTransfer.lean` — authored.
   `torsionDefectTransferStatement_of_countable` (from the closed `manuscriptTorsionComplementaryIdempotents`),
   `printedDynamicRankBudget_of_residuals` (assembly without that piece).

## Residual piece Props (exact names in `DynamicRankBudget.lean`; each quantifies over every nonempty compact
## metrizable zero-dimensional `X`, `T : X ≃ₜ X`, finite field `k`)

| Prop | content | owner |
|---|---|---|
| `CoreRingReflectionStatement` | `R_X` DF ⟺ SF ⟺ LEF ⟺ `∀ x, x ∈ CR(T)` | chain-reflection |
| `CoreModelsLEFStatement` | `IsLEFRing R_Y` | chain-itinerary |
| `CountableCrossedProductStatement` | `Countable R_X` | chain-core |
| `CoreMFRadicalKillStatement` | over `F_2`: `K_n(I) ≤ Rad_MF(GL_n)` (n ≥ 3), `EL_n ∩ K_n(I) ≤ Rad_MF(EL_n)` (n ≥ 4), `K_n(I)` locally finite (n ≥ 2) | chain-radical |
| `BilateralThreeTransferStatement` | `R_X` not DF ⇒ `∃ x ∈ Rad_MF(GL_n(R_X)), x ≠ 1` (n ≥ 3) | ct-bilateral-mf |
| `TorsionDefectTransferStatement` | same for `EL_n`, n ≥ 4 | ct-rank-budget (module 3) |
| `UnitKernelLocallyFiniteStatement` | `K_1(I)` locally finite over `F_2` | ct-involution |
| `ReturnEmbeddingStatement` | no periods below `r` ⇒ a return system `(C, S)`: injective non-unital `R_X → M_m(R_C)`; injective `GL_{nr}(R_C) → GL_n(R_X)`, `EL_{nr}(R_C) → EL_n(R_X)` (n ≥ 2), `GL_r(R_C) → R_X^×`; over `F_2`, every element of the core kernel of `GL_n(R_X)` / `EL_n(R_X)` / `R_X^×` is conjugate into the image of the core kernel of the embedded group | ct-return-tower (tower), ct-involution (involution), ct-rank-budget (induced core, `J`, placement) |

## Next

- Land module 2 when green; probe and land module 3; census rows for tex 1696–1705, 1743–1766, 254–259 (partial over
  the residuals above).
- Then my share of `ReturnEmbeddingStatement`: the induced core `CR(S_C) = C ∩ CR(T)` and the phase-zero placement,
  once ct-return-tower names the return system.

## Progress log

- 09-13 ~16:35: plan landed (ae6756df1).
- 09-13 16:40: MFRadicalTransport LANDED fbd3fae3c.
- 09-13 16:46: DynamicRankBudget probe 0913-164602-2510 FAILED (one injectivity term); fixed.
- 09-13 17:00: DynamicRankBudget LANDED a2cb17f58 (GREEN 0913-165527-31471); census rows landed 87a9e0862.
- 09-13 17:05: DynamicRankBudgetTorsionTransfer LANDED aadb514ad (GREEN 0913-165831-41224):
  `TorsionDefectTransferStatement` is closed over `CountableCrossedProductStatement`; residual list is now items
  1–5 and 7 of the table (not `TorsionDefectTransferStatement`).
- Open for this lane: the induced core `CR(S_C) = C ∩ CR(T)` and `J = p_C I p_C` inside `ReturnEmbeddingStatement`.
  ct-return-tower's statements landed 4d2084188 (`ReturnTowerStatements`: `NoShortPeriods`, `IsReturnSection`,
  `ReturnGapsIn`, `returnTime`, `FirstReturnStatement`, `ReturnRingCrossedProductStatement`,
  `ReturnTowerUnitsStatement`; `τ.phi`, `τ.unitize`, `τ.unitizeGL`).  ct-involution's in-flight
  `ReturnPlacement.lean` is the fresh-coordinate matching of lem:involution-localization (tex 1673–1686), not the
  phase-zero placement of `K_n(J)` under `Φ` (tex 1754–1755); no overlap.  Next: state `CR(S_C) = C ∩ CR(T)`,
  `J = p_C I p_C` and the placement over those names, and bridge `ReturnEmbeddingStatement` to them.
