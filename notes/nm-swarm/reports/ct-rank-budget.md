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
3. `GroupApproximation/Manuscript/NonMFSentences/DynamicRankBudgetTorsionTransfer.lean` — LANDED aadb514ad.
   `torsionDefectTransferStatement_of_countable`, `printedDynamicRankBudget_of_residuals`.
4. `DynamicRankBudgetPlacement` 14e45f292, `DynamicRankBudgetInducedCore` 0ff627d8e, `DynamicRankBudgetReturnKernel`
   c9899b2b6, `DynamicRankBudgetReturnBridge` 4cc9a1f20, `DynamicRankBudgetReturnTransientIdeal` e2d3c56f7,
   `DynamicRankBudgetAssembly` b818e32b3 / 16937ecac (see the log below).

The piece Props of `printedDynamicRankBudget_of_pieces` (`CoreRingReflectionStatement`, `CoreModelsLEFStatement`,
`CountableCrossedProductStatement`, `CoreMFRadicalKillStatement`, `BilateralThreeTransferStatement`,
`TorsionDefectTransferStatement`, `UnitKernelLocallyFiniteStatement`, `ReturnEmbeddingStatement`) are stated in
`DynamicRankBudget.lean`; which of them are still open is in "Remaining open inputs" at the end.

## Progress log

- 09-13 ~16:35: plan landed (ae6756df1).
- 09-13 16:40: MFRadicalTransport LANDED fbd3fae3c.
- 09-13 16:46: DynamicRankBudget probe 0913-164602-2510 FAILED (one injectivity term); fixed.
- 09-13 17:00: DynamicRankBudget LANDED a2cb17f58 (GREEN 0913-165527-31471); census rows landed 87a9e0862.
- 09-13 17:05: DynamicRankBudgetTorsionTransfer LANDED aadb514ad (GREEN 0913-165831-41224):
  `TorsionDefectTransferStatement` is closed over `CountableCrossedProductStatement`; residual list is now items
  1–5 and 7 of the table (not `TorsionDefectTransferStatement`).
- 09-13 17:55: DynamicRankBudgetPlacement LANDED 14e45f292 (GREEN 0913-175226-46007): `IsCornerDeviation`,
  `cornerOf`, `placement`, `placementUnit`, `unitizeGL_placementUnit`, `coe_placement_sub_one_apply`
  (tex 1754–1755 for any return tower with `a_0 = b_0 = p_C`).
- 09-13 18:01: DynamicRankBudgetInducedCore LANDED 0ff627d8e (GREEN 0913-175920-74172):
  `coe_mem_chainRecurrentSet_of_firstReturn` (`CR(S_C) ⊆ C ∩ CR(T)`, direct chain route, not the printed saturation).
- Next: `DynamicRankBudgetReturnKernel` (transport of the placement along ct-bilateral-mf's `blockTransport`,
  deviations in the return transient ideal) and `DynamicRankBudgetReturnBridge` (`returnEmbeddingStatement_of_pieces`
  over `ReturnRingCrossedProductStatement`, `InvolutionLocalizationMatrixClause`, `CoreKernelElementaryStatement` and the
  J piece `θ⁻¹(p_C I p_C) ⊆ I_C`).
- 09-13 18:12: DynamicRankBudgetReturnKernel LANDED c9899b2b6 (GREEN 0913-180852-10846): `glEmbedding_returnPlacement`,
  `returnPlacement_sub_one_mem`, `units_map_mapMatrix_eq_one_of_forall_mem_ker`.
- 09-13 18:27: DynamicRankBudgetReturnBridge LANDED 4cc9a1f20 (GREEN 0913-182431-19490):
  `returnEmbeddingStatement_of_pieces (hring : ReturnRingCrossedProductStatement)
  (hinv : ClopenCrossedProduct.InvolutionLocalizationMatrixClause) (hkerEL : ClopenCrossedProduct.CoreKernelElementaryStatement)
  (hJ : ReturnTransientIdealStatement) : ReturnEmbeddingStatement`; `returnTowerUnits_a_zero/_b_zero`, `noShortPeriods_of_iterate`.
- 09-13 19:02: DynamicRankBudgetReturnTransientIdeal LANDED e2d3c56f7 (GREEN 0913-185556-62721):
  `returnTransientIdealStatement_holds : ReturnTransientIdealStatement` (closed). `theta_eq_returnRingHom` identifies the
  printed θ with the landed `returnRingHom`, and the zeroth coefficient is read off `coeff_one_coe_returnRingHom`.
  A first landing at 18:59 failed on a ref lock; its wire-queue line was retracted in place and re-queued at e2d3c56f7.
- 09-13 19:06: DynamicRankBudgetAssembly LANDED b818e32b3 (GREEN 0913-190003-80821): `printedDynamicRankBudget_of_openPieces`,
  `printedIntroductionAperiodicSentence_of_openPieces`.
- 09-13 19:10: assembly edit LANDED 16937ecac (GREEN 0913-190738-27144), adding the closed endpoints `returnEmbeddingStatement_holds : ReturnEmbeddingStatement` and
  `torsionDefectTransferStatement_holds : TorsionDefectTransferStatement`.

- 09-13 19:50: ChainCoreClosures LANDED b09de1dcf (GREEN 0913-194250-26824), after ms-core-2 closed
  `coreModelsLEFStatement` (b7e521e57). Closed endpoints, each with `#audit_closed_axioms`, namespace
  `GroupApproximation.ChainCore.ChainCoreClosures`: `printedBilateralThree_closed`,
  `printedIntroDirectlyFiniteIffGLThreeMF_closed`, `bilateralThreeTransferStatement_holds`,
  `coreRingReflectionStatement_holds`, `printedCoreRingReflection_closed`, `coreMFRadicalKillStatement_holds`,
  `printedCoreMFRadical_closed`, **`printedDynamicRankBudget_closed`**, **`printedIntroductionAperiodicSentence_closed`**,
  `printedTwoEndedUnitsLEFGLThreeNotMF_closed`.
- 09-13 19:52: census regrade on the lead's order (LANDED 2fb94570a): 15 rows of ct-bilateral-mf, ms-core-4, ct-return-tower and ct-two-ended
  (partial over CoreModelsLEFStatement / PrintedBilateralThree only) now name these endpoints; my own rows regraded after.

- 09-13 20:30: DynamicRankBudgetInducedCoreClosed LANDED 2829a1eb9 (GREEN 0913-202257-47589), on main's go-ahead:
  `PrintedInducedCore` (tex 1743, "The induced core is C ∩ Y": `Subtype.val '' CR(S_C) = C ∩ CR(T)` for every return
  section) and `printedInducedCore_closed` (`#audit_closed_axioms`), over ms-core-1's
  `image_chainRecurrentSet_firstReturn_printed` with `coreRingReflectionStatement_holds` and `coreModelsLEFStatement`.
  Route checked against tex 1743–1749. `mem_chainRecurrentSet_firstReturn_of_pieces` (c56f96a99) says the return ring of
  `C ∩ Y` is a corner of the LEF ring `R_Y`, then applies thm:core-ring-reflection.
  `coe_mem_chainRecurrentSet_of_firstReturn_of_pieces` (afa5cd02d) saturates through the towers, gets a corner of a matrix
  ring over an LEF ring, then applies thm:core-ring-reflection. Census LINE:1743 → formalized.

- 09-13 21:30: CLAIM (coordinator item "the 12 unassigned census sentences", merge 3 3f3f4c5c3). ct-rank-budget takes
  the four tex-1743 sentences that my `LINE:1743` row (which keys only the block's first sentence) does not cover:
  `7da9f1c6076f` ("its return ring is a corner of the LEF ring R_Y …"), `8f8f0c7b59fa` ("saturating that core through
  the finite towers …"), `d5dcf496d149` ("Theorem core-ring-reflection applied to this subsystem …"), `e7f732e9cb78`
  ("The return transient ideal is therefore J=p_C I p_C").  Plan: one module with a named closed Prop per sentence at
  the printed generality (every finite field), hex-keyed rows.  Handed off: `d59fc0887768` (tex 1341) to ms-core-1;
  the seven ct-block keys already graded by ct-sentences at ba2a9baf2 (after merge 3's base) need no handoff.

- 09-13 23:25: DynamicRankBudgetInducedCoreSentences LANDED 6387112a8 (GREEN 0913-214345-31217; import closure unchanged
  since the probe base).  Closed endpoints, each with `#audit_closed_axioms`, namespace
  `GroupApproximation.ChainCore.DynamicRankBudget`, at the printed generality (every return section, every finite field):
  - `printedInducedCoreCorner_closed : PrintedInducedCoreCorner` (key 7da9f1c6076f)
  - `printedCoreSaturationLEF_closed : PrintedCoreSaturationLEF` (key 8f8f0c7b59fa), via
    `exists_corner_matrix_returnSaturation`
  - `printedCoreSaturationRecurrent_closed : PrintedCoreSaturationRecurrent` (key d5dcf496d149)
  - `printedReturnTransientIdeal_closed : PrintedReturnTransientIdeal` (key e7f732e9cb78): both directions of J = p_C I p_C
  Census rows appended (formalized, queued for wiring).  Of the merge-3 unassigned keys: ct-sentences' seven resolved at
  merge 4 (0e622f840); `d59fc0887768` (tex 1341) re-sent to ms-core-1 after the restart.

- 09-14: CLAIM, on the coordinator's reassignment: census key `d59fc0887768` (tex 1341, sec:chain-core preamble, "The
  torsion-defect argument can identify the whole MF radical even when the defect ideal is proper"), previously handed to
  ms-core-1.  Plan: a named closed Prop over `printedCoreMFRadical_closed`, adding that the defect ideal is proper, and
  a hex-keyed row.

- 09-14 00:32: ChainCoreOpeningSentence LANDED 10faf76cf (GREEN 0914-002813-94264): `printedChainCoreOpening_closed :
  PrintedChainCoreOpening` (key d59fc0887768, tex 1341), with `#audit_closed_axioms`.  Over every finite field the defect
  ideal equals I (`defectIdeal_eq_transientIdeal_chainRecurrentSet`) and is proper (CR(T) nonempty, so 1 ∉ I).  Over F_2,
  Rad_MF(GL_n) = K_n = EL_n(R_X, I) for n ≥ 3 and Rad_MF(EL_n) = EL_n(R_X, I) for n ≥ 4 (`printedCoreMFRadical_closed`).
  Row appended.  ms-core-1 dropped the key and withdrew its uncompiled draft.  Merge 5 (a4f8d4b82) had this as the only
  unassigned sentence.

**cor:dynamic-rank-budget is closed** (`printedDynamicRankBudget_closed`); the three inputs below are closed by
`coreRingReflectionStatement_holds`, `coreModelsLEFStatement`, `coreMFRadicalKillStatement_holds`.

## Formerly open inputs of cor:dynamic-rank-budget (exact names, in `DynamicRankBudget.lean`)

| Prop | content | owner |
|---|---|---|
| `CoreRingReflectionStatement` | `R_X` DF ⟺ SF ⟺ `IsLEFRing` ⟺ `∀ x, x ∈ CR(T)` | chain-reflection, ct-return-tower |
| `CoreModelsLEFStatement` | `IsLEFRing R_Y` | chain-itinerary |
| `CoreMFRadicalKillStatement` | over `F_2`: `K_n(I) ≤ Rad_MF(GL_n)` (n ≥ 3), `EL_n ∩ K_n(I) ≤ Rad_MF(EL_n)` (n ≥ 4), `K_n(I)` locally finite (n ≥ 2) | chain-radical, ms-core-4, ms-core-5 |

Closed by producers on main: `CountableCrossedProductStatement` (ms-core-4), `BilateralThreeTransferStatement` over
`CoreModelsLEFStatement` (ct-bilateral-mf), `TorsionDefectTransferStatement`, `UnitKernelLocallyFiniteStatement`
(ct-involution), `ReturnEmbeddingStatement` (this lane, over ct-return-tower, ct-involution, ct-bilateral-mf).

- Open for this lane afterwards: nothing owned; the printed saturation route and the reverse inclusion for tex 1743–1750
  went to ms-core-1.
  ct-return-tower's statements landed 4d2084188 (`ReturnTowerStatements`: `NoShortPeriods`, `IsReturnSection`,
  `ReturnGapsIn`, `returnTime`, `FirstReturnStatement`, `ReturnRingCrossedProductStatement`,
  `ReturnTowerUnitsStatement`; `τ.phi`, `τ.unitize`, `τ.unitizeGL`).  ct-involution's in-flight
  `ReturnPlacement.lean` is the fresh-coordinate matching of lem:involution-localization (tex 1673–1686), not the
  phase-zero placement of `K_n(J)` under `Φ` (tex 1754–1755); no overlap.  Next: state `CR(S_C) = C ∩ CR(T)`,
  `J = p_C I p_C` and the placement over those names, and bridge `ReturnEmbeddingStatement` to them.
