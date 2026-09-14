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

## thm:core-ring-reflection (tex 1516–1540): printed assembly — LANDED 17817cdac

Module `GroupApproximation.Manuscript.NonMFSentences.CoreRingReflection` (chain-reflection's planned module 3;
probe 0913-185808-72846 GREEN, BUILT line checked, 0 errors, queued for wiring), namespace
`GroupApproximation.ChainCore.CoreRingReflection`:
- closed (`#audit_closed_axioms`, axioms ⊆ {propext, Classical.choice, Quot.sound}):
  - `printedCoreKillsDefectsAndI : PrintedCoreKillsDefectsAndI` (tex 1527–1528, "A unital homomorphism to a directly
    finite ring kills every d ..., hence all of I"), via `killsKernelOfDirectlyFinite_restrict`
    (`transientIdeal_chainRecurrentSet_eq_span` + `map_defectD_eq_zero`);
  - `printedCoreIZeroIff : PrintedCoreIZeroIff` (tex 1538, "I = 0 exactly when X = Y"), via `transientIdeal_eq_bot_iff`;
  - `restrict_surjective_of_isClosed` (restriction to a closed invariant set is onto; extension of LC functions).
- over the named `DynamicRankBudget.CoreModelsLEFStatement` ("R_Y is LEF", building: ms-core-2, ms-traces-3):
  - `printedCoreRingReflection_of_coreModels : PrintedCoreRingReflection` (tex 1516–1523, one conjunct per printed
    sentence: the universal directly finite / stably finite / LEF quotients, the `M_m` amplification, and
    DF ⇔ SF ⇔ LEF ⇔ every point chain recurrent), through chain-reflection's `isUniversalQuotients_of_surjective`,
    `isUniversalQuotients_mapMatrix`, `directlyFinite_iff_stablyFinite_iff_lef_iff_injective` and `restrict_injective_iff`;
  - `coreRingReflectionStatement_of_coreModels : DynamicRankBudget.CoreRingReflectionStatement` (ct-rank-budget's piece).
- Agreed with ct-bilateral-mf (one message): its DF ⇒ LEF and nonzero-defect wrappers stay in
  `Manuscript/ChainCore/BilateralThreeCoreModels` (511dec7d2); this module defines neither.
- Unowned duplicate on disk: `GroupApproximation/Dynamics/ClopenCoreReflection.lean` (unlanded since 17:25, no `.files`
  owner, interface Props and model tests only; noted by ms-core-5). Not touched.
- Census rows (keys from ms-core-4's ledger adbf70b62): `42c043ef7ab5`, `8981cd70915a`, `43afa4ee3f10`, `cfbacaa0fffa`,
  `400dde0dbd9d` partial over CoreModelsLEFStatement; `9dae685e37b9`, `b23e0f5197b5` formalized.

## V3 residual 3: `OsinLemma94ClassCaseGapEndpointStatement` (claimed from ct-bilateral-cell; statement at 55d5916c7)

Module `GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassPairShapes` (ct-bilateral-cell) states the three
shapes; the assembly `osinLemma94ClassCases_of_residuals` (`OsinLemma94ClassPairTransfer`) takes this Prop as `hendpoint`.

- LANDED 1de75b6a0 `Estimating/OsinLemma94ClassGapEndpointModel` (probe 0913-195149-70727 GREEN): `SideAt.word_split`,
  `gap_length_le` / `inGap_gap_length_le` (a gap of an N1 ∪ N2 class has ≤ B = ⌈(c+2)/λ⌉₊ letters),
  `ofSides_not_inGap`, `ofSides_not_gapEndpoint` (the shape is empty on singleton classes).
- LANDED 2fc90db55 `Estimating/OsinLemma94ClassGapHairModel` (probe 0913-203755-64088 GREEN): `isLambdaCQuasiGeodesicWord_hair`,
  `isLambdaCQuasiGeodesicWord_hair_add_two`, `Surgery.InnerGRegion.not_mem_cycle_of_relatorCell`,
  `not_mem_cycle_of_outer`, `hair_not_mem_cycle`.

Finding (an obstruction to the route, not a refutation).  The producer route merges the polygon face with the faces
inside the gap loops (`Surgery.InnerGRegion`), so gap vertices become corners of one merged G-face, and runs the Case 1
surgery (`exists_quadrilateral_region_rotate`) there.  A HAIR gap defeats it: a cell reading `p, h, α h, q` with both
darts of `h` on the cell gives the class `[α q] ++ [h, α h] ++ [α p]` (Maximal holds, the gap has value one, the tip is
`InGap`), and hair words pass the quasi-geodesic clauses (always for class words, for relator words and sections once
c ≥ 2λ).  Darts on a relator cell or on the exterior lie on no merged boundary, so no merged face has a hair tip as a
corner.  Moving the endpoint to the hair base costs up to B/2 on a connector, and pairs carry one threshold.

Pieces of the bubble route (gap darts on G-faces): (i) the gap loop bounds a disc face set; (ii) it holds no relator
cell (short boundary against 9.7(b) below; pocket diagram for simple loops, ms-traces-2's
`ClosedWalkEnclosedSubdiagramStatement` (a5dc9e6b0) otherwise); (iii) it meets no selected region; (iv) the merged walk
reads the class words; (v) cutting targets, claimed by ms-compress-3 as `OsinLemma94ClassCaseGapEndpointCuttingStatement`
in its own module.  Bubble-route statements are held pending main's ruling on the hair case: (R1) restrict the class
cases to classes whose gap darts lie on G-faces, with the count piece producing such classes, or (R2) two thresholds
on the metric half's pairs (segments above ε + B, connectors below ε − B), which moves gap endpoints to corners and
makes this residual unnecessary.

### Ruling 23:12: R2 (two thresholds); GapEndpoint leaves the waist, GapSpan stays

Gate (checked before building): the metric half's pairs come from `unboundOrientedWordPolygonMonotone` through
`OsinUnboundScale.orientedWordSidePair_of_orientedClassPair`.  The cross distances are bounded through
`OsinUnboundScale.epsilon_large`, `12 ((δ + 6) + 1) + 2 κ < ε`, with the Morse radius `κ` of
`exists_word_replacement_morse_monotone` depending on `δ, λ, c` only.  The segments are bounded through
`shortcut_shortens`, `ε < β − 2 κ` with `β = (λ √ρ / 240 − c) / 1000`, and `ρ` is chosen after `ε`
(`exists_osinUnboundScale_after_epsilon`).  So `ε₀ > 12 ((δ + 6) + 1) + 2 κ + B` and a scale at `ε + B` deliver
connectors below `ε − B` and segments above `ε + B`, in the order of Osin's (36).  R2 passes the gate.

Interface agreed with ct-bilateral-cell (one message each way): ct-bilateral-cell owns
`Estimating/UnboundOrientedWordPolygonTwoThreshold` (`OrientedWordSidePairTwo`, `unboundOrientedWordPolygonMonotoneTwo`),
`Estimating/OsinLemma94ClassSectionTwoThreshold` (`OsinLemma94DensePolygonsAntiparallelTwo`,
`osinLemma94AntiparallelMetricTwo`, `OsinLemma94ClassCasesTwoThresholdInput` over pairs at `ε − B` with segments above
`ε + B`, `osinLemma94Section_of_classCountTwoThreshold`) and `osinLemma94ClassCasesTwoThreshold_of_residuals`.  This lane
owns the corner move:

- LANDED 9133128ae `Estimating/OsinLemma94ClassCornerMove` (probe 0914-005607-41763 GREEN, BUILT line checked, 0 errors;
  queued for wiring): `SideAt.eq_or_block_le` (two sides of one class
  are equal with equal offsets, or one block ends before the other starts), `not_inGap_corner`, `wordDist_vertex_le_of_near`,
  `exists_cornerMove` (a position moves to a position inside no gap by ≤ ⌊B/2⌋), and
  `OsinLemma94ClassPolygons.exists_cornerPair_of_twoThreshold (Q) (hlambda : 0 < lambda) (k) (C : WordConnectorPair …
  (eps - ⌈(c + 2) / lambda⌉₊)) (hlongS) (hlongT) (hback) : ∃ C' : WordConnectorPair … eps, C'.b' < C'.b ∧
  ¬ Q.GapEndpoint k C' ∧ C'.source = C.source ∧ C'.target = C.target`.

Correction 23:2x (main, from ct-bilateral-cell): corner moves do not reduce GapSpan to single-side pairs (a backwards pair
spanning a hair gap between two short sides; linearly many backtracks when λ < 1).  `OsinLemma94ClassCaseGapSpanStatement`
stays a residual with a geometric producer (ct-bilateral-cell: `SurgeryCellHairThickening`, `InnerGRegion`,
`exists_quadrilateral_region_rotate`).  ms-compress-3's piece-(v) model (d2a74aca5) stays as calibration.

## V5 residual 9: binder 6's two-arc producer `OsinSectionPocketFaceSetTwoArcSectionStatement` (coordinator 01:4x / 08:4x)

For w1-binder-7's route 3 (f81311dc9).  Statement split agreed with w1-binder-6 (owner of binder 6's full-t₁ case) in one
message each way.

- LANDED 2a4d58ae6 `Estimating/OsinPocketTwoArcSection` (probe 0914-084029-91682 GREEN, BUILT line checked, 0 errors; queued
  for wiring):
  - `SectionCuts.SpansWhole cuts j` (`cut j = 0 ∧ cut (j+1) = |∂Δ|`), `SectionCuts.cut_sub_lt_of_not_spansWhole`,
    `SectionCuts.not_spansWhole_of_ne` (a nonempty other section: the count ≥ 2 case), `SectionCuts.spansWhole_of_count_eq_one`.
  - Residual `SectionPocketFaceSetWholeSectionTwoArcInput` / `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`: the
    two-arc producer at a section spanning the whole boundary.
  - `sectionPocketFaceSetTwoArcInput_of_proper_of_wholeSection (hproper) (hwhole)` and
    `osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection (hproper : OsinSectionPocketFaceSetProperSectionStatement)
    (hwhole : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement) : OsinSectionPocketFaceSetTwoArcSectionStatement`.
    Outside whole sections `t₂.length ≤ cut (j+1) − cut j < |∂Δ|` (`lo_le`, `le_hi`, O-equivalence keeps `|∂Δ|`).
- Why the whole section is the residual: `PocketWalk.exists_of_exteriorAt` runs `t₂` from the start of the first region's target
  arc to the end of the second's; at a whole section that is all of `∂Δ` when those arcs touch positions `0` and `|∂Δ|`, the two
  sides meeting at the base vertex.  `PocketFaceSet` positions are linear (`start + length ≤ hi`), so the short pocket across the
  base vertex is not expressible.
- Model LANDED 1478083b7 (probe 0914-085400-96548 GREEN, BUILT line checked, 0 errors, `#audit_closed_axioms`; queued for
  wiring): `Estimating/OsinPocketWholeSectionWrapModel`, a least-area labelled three-petal rose over `Perm (Fin 3)`
  (faces `Π = [0,2]`, `F = [1]`, `K = [3,5]`, exterior `[4]`; `|∂Δ| = 1`).  `wrapK eps`: at every `ε` a pocket face set in walk
  order with empty sides, proper `t₁ = [2]` and `t₂ = ∂Δ` (`wholeSectionWrapModel`).  So the whole-section wrap with a proper
  source arc occurs.  Calibration (`properK`): at `ε ≥ 1` the same face set with the exterior dart read as a side has an empty,
  proper `t₂`, so the model neither refutes nor proves the residual; it carries no section family.
- Candidate producer route for the residual (not built): the inner pocket between the two regions, excluding them (sides
  `x.leftSide`, `y.rightSide`, `t₁` the gap arc, `t₂ = [end x, start y]`), has proper arcs because the regions' arcs are nonempty;
  it needs the same kept-cell and noncrossing pieces as the landed walk producer.

## Census rows

`metadata/nm-census-rows/ct-return-tower.tsv` LANDED 988ae81b2: tex 1710, 1716, 1717, 1719, 1721, 1722, 1727, 1731, 1732,
1734, 1739, 1740.  Pending: 1709 (after ReturnCells lands), 1723 and 1726 (after the ring iso).

## Progress log

- 09-13 16:37: ReturnTowerUnits GREEN (first probe), LANDED 28cd138ca.
- 09-13 16:48: ReturnTowerStatements GREEN after an import fix, LANDED 4d2084188.
- 09-13 17:06: ReturnSection and FirstReturnMap GREEN, LANDED e4a681074; both Props closed.
