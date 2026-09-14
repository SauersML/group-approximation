# Lane ms-traces-2: tex 1856–1976 (prop:locally-rf-by-z-trace, the construction of W, eq:affine-clifford-witness)

Lead: session nonsofic-existence-49 (wave 2, ROSTER-wave2 Brief R). Snapshot: origin/main 5b3910136 (tex 2507 lines).

## Ledger

All 29 census rows of the range were matched by text against the current tex. None drifted: the census is keyed at
the pre-chain-core hash, but these sentences did not change. Every sentence of tex 1856–1975 has a row. Carriers are
root-imported and audited in `Manuscript/NonMF/Audit/Sec4.lean`. `#audit_axioms` throws on non-classical axioms and
`#audit_closed_axioms` also refuses leading binders. The Analysis chain of the proposition has no Prop binder standing
for a cited result.

| key | tex | status | carrier | verdict |
|---|---|---|---|---|
| a817c6ae86c9 | 1856–1857 | definition | `LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite` | PASS; the row is ms-traces-1's (range 1808–1858), which also graded it PASS |
| fd8372f71c2d | 1861–1862 | formalized | `AmenableExtensionTrace.manuscriptPrintedAmenableExtensionTrace` | PASS: closed endpoint. A normal `N ≤ G`, `G` countable, `G ⧸ N` amenable (`Nonempty InvariantMean`) is the printed extension up to isomorphism |
| 0bd25ebcbeac | 1862–1864 | formalized | same | PASS: `IsQuasidiagonalTrace τ_N ∧ IsAmenableTrace τ_G` |
| d47b613bb096 | 1869–1872 | structural | overview | PASS |
| a97f0ab46cd9 | 1873–1875 | formalized | `AmenableExtensionSentences.manuscriptSentence_cocycleValues` | PASS |
| 94ebd1377c15 | 1876–1879 | formalized | same | PASS (`b = esCocycleN`, `σ = sect`) |
| 6e563dbca22b | 1880–1883 | formalized | `manuscriptSentence_cocyclePacketSeparates` | PASS |
| 30eb3e57ac10 | 1884–1888 | formalized | `manuscriptSentence_cosetsDistinct`, `..._compressionUCPAndTranslation` | PASS |
| da2fd300384a | 1888–1892 | formalized | `manuscriptSentence_compressionUCPAndTranslation` | GAP G5: the carrier gives `g • σ(x)r_qΛ ∈ T`, not the printed formula `gσ(x)r_qΛ = σ(ḡx)r_{θ(b(g,x))q}Λ` |
| 89bc31ec5034 | 1893–1900 | formalized | `manuscriptSentence_rankBoundGivesHS` | GAP G3: the printed identity `Φ(u_gh)−Φ(u_g)Φ(u_h) = Πλ(g)(1−Π)λ(h)Π` and the printed display `‖·‖₂² ≤ \|{x∈F : h̄x∉F}\|/\|F\|` are not stated; the carrier bounds by `√(1/(n+1))` |
| 1ea7f92c66a1 | 1901–1905 | formalized | `manuscriptSentence_traceIsFixedPointFraction` | GAP G2: "trace = fraction of fixed points of T" is not stated for general g, and the two printed cases (ḡ≠1 moves the F-coordinate; ḡ=1 gives θ(b(g,x))q≠q) are replaced by a one-step argument (see the docstring of `AmenableExtensionAmenableTrace`) |
| b77ceccea9ed | 1906–1911 | formalized | `manuscriptSentence_folnerLimitsExtend` | PASS |
| 23d58dbda4bf | 1913–1917 | formalized | `manuscriptSentence_stage*` | PASS |
| 8e53d32e3fb8 | 1920–1923 | structural | `AmenableTraceSentencesB.manuscriptSentence_defectFactorization`, `CliffordWitnessDirectDefect.signSubgroup_le_printedDefect` | GAP G4: the sentence asserts that 𝔇_W(Γ) contains a commutator whose square is a central involution. The pieces exist (`pointDefect = ⁅x, ι a⁆`, `pointDefect_mem_printedDefect`, `sign_eq_pointDefect_sq`, `signAmbient_central/_sq/_ne_one`), but no declaration states the sentence, so the row is graded `structural` while it asserts mathematics |
| 60898a519f4f | 1923–1926 | definition | `CliffordWitnessDirectDefect.PrintedCliffordWitnessNotIsOperatorMF` | PASS (countable Γ with (T), injective α, a ∉ range α) |
| c180c0186454 | 1926–1932 | definition | `MappingTelescope.Telescope`, `MarkedCompression.Vertical` | PASS (`V = T_α ⋊[shift] ℤ`) |
| d5c52ca23af0 | 1933–1935 | formalized | `CliffordConstructionSentences.manuscriptSentence_hnnExtension` | GAP G1: the carrier gives `tι(g)t⁻¹ = ι(αg)` and that every element of T_α sits at some level. Missing: (a) "V is the ascending HNN extension of Γ along α", i.e. `V ≃* HNNExtension Γ ⊤ α.range` with `t ↦ t`, `ι ↦ of` (`MarkedCompressionGroup`'s docstring asserts this without proof); (b) `T_α = ⋃_{n≥0} t^{-n}Γt^n` inside V (`inl_level_succ` is the step, not the union) |
| 08844a3bdb91 | 1936 | definition | `MarkedCompression.Cosets`, `rootCoset` | PASS |
| 86ba78fb0d96 | 1936–1942 | formalized | `manuscriptSentence_cliffordLampPresentation` | PASS: `CliffordLamp X := PresentedGroup (relators X)` |
| 4cbf47e489a6 | 1943–1945 | structural | `CliffordLamp.crossing` | PASS: `crossing f g = Σ_x Σ_{y<x} f x * g y`, the printed `B(f,g) = Σ_{x>y} f(x)g(y)` |
| dc43ec6b23ed | 1945–1948 | formalized | `manuscriptSentence_signedModelGroupLaw` | PASS; the row should also name `CliffordLamp.crossing_add_left/_right` (the printed "since B is bilinear") |
| 4704b74b6c8e | 1949–1952 | formalized | same | PASS |
| 1fab0dcc8e88 | 1953–1954 | formalized | `manuscriptSentence_toModelHomomorphism` | PASS |
| b9ca7188b1f5 | 1954–1959 | formalized | `manuscriptSentence_cliffordLampNormalForm` | PASS: `section' ⟨a, f⟩ = signPow a * wordOfSupport f.support`, and `wordOfSupport s = wordOfList (s.sort (· ≤ ·))` (CliffordLampNormalFormSplice:126) is the printed `ε^a c_{x₁}⋯c_{x_r}` with `x₁ < ⋯ < x_r` |
| 407925e64c6c | 1960–1961 | formalized | same | PASS |
| 51284d178433 | 1962–1964 | formalized | `manuscriptSentence_cliffordLampCountableLocallyFinite` | PASS |
| c41bad22d29b | 1964–1968 | formalized | `manuscriptSentence_cliffordLampKillSignCentralExtension`, `..._wCentralExtensionOfWreath` | PASS |
| ad753104ce33 | 1968–1971 | formalized | `manuscriptSentence_permutationAutomorphism` | PASS (`permHom : Equiv.Perm X →* MulAut (CliffordLamp X)`) |
| 5306701b688c | 1971–1975 | formalized | `manuscriptSentence_verticalActsOnLamp` | PASS (`lampAction : Vertical →* MulAut`; `Ambient` = lamps ⋊ Vertical) |

## Gaps and plan

G1–G5 get new carrier modules. Ownership check done 17:0x: no lane `.files` lists these carriers; the paths are free on
disk and on origin; the adjacent lanes are ms-traces-1 (tex 1808–1858) and ms-traces-3 (1977–2106).

- CLAIM G4 `GroupApproximation/Manuscript/NonMFSentences/CliffordDefectCommutatorSentence.lean`: the sentence at tex
  1920–1923 (𝔇_W(Γ) contains the commutator `d = [tct⁻¹, a]` with `d²` a central involution; `⟨ε⟩` is a finite central
  subgroup inside 𝔇_W(Γ)).
- CLAIM G2, G3, G5 `GroupApproximation/Analysis/AmenableExtensionPrintedSteps.lean`: the printed translation formula,
  the coordinate form of `Φ(u_gh)−Φ(u_g)Φ(u_h) = Πλ(g)(1−Π)λ(h)Π`, the printed display
  `‖·‖₂² ≤ |{x∈F : h̄x∉F}|/|F|`, the trace as the fixed-point ratio, and the two printed cases.
- CLAIM G1 `GroupApproximation/Sofic/VerticalAscendingHNN.lean`: `V ≃* HNNExtension Γ ⊤ α.range` (`t ↦ t`, `ι ↦ of`) and
  `T_α = ⋃_{n≥0} t^{-n}Γt^n` inside V.

## Item 2 (main ~18:45): binder 3's island case, helping ms-intro-1

Context: a Case 1 X-walk `X₁ t X₂ t⁻¹ X₃` runs through a cutting path t around an island that holds a relator cell. The
pocket side is disconnected across t, so it is not a PocketRegion, and the walk is not simple. Main's ruling: ms-intro-1
lands `OsinLemma94CaseOneIslandStatement`; the loop cut comes from the enclosed singular subdiagram of the closed walk,
Osin's Γ joined along t. I proposed the split to ms-intro-1 in one direct message (~18:50): ms-intro-1 owns the island
statement, its reduction and the audit of `ofPlanar`, `isRelatorProduct_of_planar`, `InnerDiscRegion` and the zero-cell
merge; this lane owns A–C below.

- CLAIM A `GroupApproximation/GGT/VanKampen/ClosedWalkEnclosedSubdiagram.lean`: `EnclosedFaceSet`,
  `ClosedWalkEnclosedSubdiagramStatement` (Ξ reads the walk, carries the enclosed relator cells, least area inherited) and
  `enclosedSubdiagram_leastAreaCut`.
- CLAIM B `GroupApproximation/GGT/VanKampen/Estimating/OsinEnclosedSubdiagramLoopCut.lean`:
  `OsinLoopCut.ofEnclosedSubdiagram`, `EnclosedSubdiagramLoopCutStatement` and `EnclosedCellTransportStatement`.
- CLAIM C `GroupApproximation/GGT/VanKampen/ClosedWalkIslandModel.lean`: a closed island model (not simple; enclosed and
  disconnected across t; calibration of Ξ).

Ownership check (~18:50): the paths and names are free on origin, in the shared tree and in every `lanes/*.files`.

## Item 3 (main ~20:15): `EnclosedLeastAreaFilterStatement`, with ms-inverses-1 helping

The disc form `DiscDiagram.LeastArea.length_filter_mem_le` collapses the region through `IsDiscRegion`. A face set
joined along a bridge has no disc region, and splitting along the bridge does not help: a filling of `X₁ t X₂ t⁻¹ X₃`
does not split into fillings of the pieces with budgets that add, so the far-component route gives no bound.

Route: thicken every bridge edge into a digon G-face. Use `FaceEdgeDoubling.diagram` on an inner face and
`OuterSpurThickening.diagram` on the exterior; both are O-equivalent, keep the walk word and keep the enclosed cells.
The bridge-free enclosed set is a pocket region, via `PocketRegion.ofNoncrossingClosedWalk` with hull-euler's
`reclosed_euler`, and the disc form applies there.

- CLAIM pieces and assembly `GroupApproximation/GGT/VanKampen/ClosedWalkEnclosedSubdiagramPieces.lean`:
  `EnclosedBridgeDoublingStatement`, `EnclosedPocketRegionStatement`, `enclosedLeastAreaFilter_of_pieces`.
- CLAIM bridge doubling `GroupApproximation/GGT/VanKampen/ClosedWalkEnclosedBridgeDoubling.lean`: the producer of
  `EnclosedBridgeDoublingStatement`, by induction on bridge darts.
- Proposed to ms-inverses-1 (~20:35, one message): `EnclosedPocketRegionStatement` (suggested path
  `ClosedWalkEnclosedPocketRegion.lean`): noncrossing pocket walk, outer cycle follows, `sideFaces = faces`.
- **FALSE PRINTED-STYLE STATEMENT (found by ms-inverses-1, ~20:50):** `EnclosedFaceSet.turn_mem` is membership-only.
  - Model: three loops at one vertex (Π₁ = [0], Π₂ = [2], Π₃ = [4], exterior [1,3,5]). The walk [1,5,3] lists them out
    of rotation order, passes every field, and has no bridges.
  - With labels over S₃×S₃, the inverse walk has a one-relator filling while Δ is least area with 3 cells. So the
    landed `EnclosedLeastAreaFilterStatement` is false, and so is the unlanded `EnclosedPocketRegionStatement`.
  - ms-inverses-1 builds the refutation (`ClosedWalkEnclosedOutOfOrderModel`).
  - Also from ms-inverses-1: island model C's Δ is not least area (its boundary value is 1), so the calibration clause
    `diagram.LeastArea → Xi.LeastArea := id` is vacuous. The model still shows the walk is not simple, that the faces
    meet only along t, and `EnclosedFaceSet`.
- Ruling (main 21:22): additive successor-form variants; the landed `EnclosedFaceSet` is not edited (ms-intro-1's
  modules import it); send the names to ms-intro-1, ms-inverses-1, w1-binder-6 and w1-binder-8 in one message.
- 21:3x written, attic-landed and probing:
  - `ClosedWalkEnclosedSucc`:
    - `EnclosedFaceSetSucc` (extends `EnclosedFaceSet` with `turn_next`: the first kept dart after
      `α outerWalk[i]` is `outerWalk[(i + 1) % outerWalk.length]`);
    - `ClosedWalkEnclosedSubdiagramSuccStatement`, `EnclosedLeastAreaFilterSuccStatement`,
      `leastArea_of_enclosedLeastAreaFilterSucc`;
    - weakenings `closedWalkEnclosedSubdiagramSucc_of_statement`, `enclosedLeastAreaFilterSucc_of_statement`.
  - `Estimating/OsinEnclosedSubdiagramLoopCutSucc`: `EnclosedSubdiagramLoopCutSuccStatement` (the same binders with
    only the face-set hypothesis changed) and `enclosedSubdiagramLoopCutSucc_of_loopCut`.
  - The pieces module, now over the Succ carrier: `EnclosedBridgeDoublingSuccStatement` (mine),
    `EnclosedPocketRegionSuccStatement` (ms-inverses-1), `enclosedLeastAreaFilterSucc_of_pieces`.

## Item 4 (main 23:12, after the coordinator restart): the successor-form route end to end

ms-intro-1 and ms-inverses-1 are not resumed; this lane owns:
1. the refutation `¬ EnclosedLeastAreaFilterStatement`;
2. the successor-form producer for noncrossing walks and the Succ X/Y pockets;
3. the Succ least-area filter and the enclosed pocket region;
and the names go to w1-binder-6 and w1-binder-8.

State at 23:2x:
- `ClosedWalkEnclosedSucc` and `Estimating/OsinEnclosedSubdiagramLoopCutSucc` LANDED d4f72d7e8 (22:01, from probe
  0913-213147-24617), queued for wiring.
- The pieces module was red at that probe (`OEquivalentDiscDiagram.leastArea` is not imported); fixed inline.
- ms-inverses-1's claimed `ClosedWalkEnclosedOutOfOrderModel` and `ClosedWalkEnclosedPocketRegion` were never written
  (not on disk, not in its `.files`, no attic copy). Both are rebuilt here from its report.
- TAKEOVER of ms-intro-1's drafts, now in this lane's `.files`:
  - `ClosedWalkEnclosedNoncrossingSucc.lean`: GREEN at 0913-213523-46026, same bytes; the producer
    `enclosedFaceSetSuccOfNoncrossing` is still to be added.
  - `Estimating/OsinLemma94SameCellPocketNoSpurSucc.lean`: the X/Y pockets over the Succ loop cut, unprobed.
- CLAIM `GroupApproximation/GGT/VanKampen/ClosedWalkEnclosedOutOfOrderModel.lean`: the out-of-order refutation.
- CLAIM `GroupApproximation/GGT/VanKampen/ClosedWalkEnclosedPocketRegion.lean`: `EnclosedPocketRegionSuccStatement`.
- 23:36 pieces probe 0913-233612-84931 GREEN → **LANDED 947100710** (queued). `enclosedLeastAreaFilterSucc_of_pieces`
  is on origin.
- 23:45 co-probe 0913-234554-9146 RED, and the fixes are written.
  - `ClosedWalkEnclosedNoncrossingSucc`: linter error on unused binder names in `turn_next`.
  - `ClosedWalkEnclosedOutOfOrderModel`: an unused simp argument and three failed rewrites:
    - `pow_add` in the relator-product induction;
    - `Even.neg_one_pow` on `ℤˣ`, now replaced by `interval_cases m` over 0, 1, 2;
    - `rw [filter_length]`: the filter statement instantiates the classical decidability instance while the concrete
      lemma found another. It now goes through the instance-generic `length_filter_of_all`.
  - `OsinLemma94SameCellPocketNoSpurSucc` was not reached.
- 23:5x written: `ClosedWalkEnclosedPocketRegion`.
  - `enclosedPocketRegionSucc : EnclosedPocketRegionSuccStatement`: `turn_next` plus `Nat.find` give a `FirstTurn`
    chain; then `FirstTurnWalk.isNoncrossingClosedWalk_reverse`, `outerCycle_followsBoundary`, `reclosed_euler` and
    `ofNoncrossingClosedWalk`.
  - `sideFaces = faces`: `sideFaces_subset` by EqvGen invariance, `subset_sideFaces` by the good-dart invariant over
    `Adjacent` and connectivity.
  - `length_filter_le_of_bridgeFree`: the Succ filter without bridges, with no doubling needed.
  - `enclosedLeastAreaFilterSucc_of_doubling`.
- ~00:0x BLOCKER, fleet-level: MSI master absent and the auth breaker set (`/tmp/msi_breaker`), so no probe runs. The
  breaker is left in place for the coordinator.
- ~00:2x MSI master back. Doubling run module written (`ClosedWalkEnclosedBridgeDoublingRun`, attic d47ea5766):
  - `sigma_eq_none_iff`, `sigma_eq_embed_iff_some_none`;
  - `firstKept_lift`, a first run to a kept dart lifts across the insertion;
  - `first_kept_unique`, `exists_first_kept_of_alpha_mem`, `walkKeep_image_iff`;
  - `turn_next_image`, the successor form of the image walk.
- ~00:3x both probes failed on infrastructure, not on Lean: 0913 probe10 at the remote `git fetch`, probe11 with the
  MSI connection down. A five-module co-probe is relaunched when the master is up.
- w1-binder-6 (Lean-verified, bda10ebe8 `OsinPocketFullArcLakeModel.not_enclosedFaceSetSucc`): at binder 6's full-t₁
  lake no outer walk is `EnclosedFaceSetSucc`. Binder 6 pivots to `PocketRegion.ofNoncrossingClosedWalkEuler`; no
  change to this route. The island model does satisfy the successor form (every turn is m = 1), so doubling stays
  needed for binder 3 and for nested same-cell pairs.
- 01:38 co-probe 0914-013843-94866:
  - `ClosedWalkEnclosedNoncrossingSucc` and `OsinLemma94SameCellPocketNoSpurSucc` BUILT → **LANDED 07911e74b** (queued):
    `enclosedFaceSetSuccOfNoncrossing`, `EnclosedFaceSetSuccOfNoncrossingStatement`,
    `osinLemma94CaseOne{X,Y}Pocket_of_enclosedLoopCutSucc` and the no-spur twins.
  - Red, fixed: `OutOfOrderModel` (`push_neg` deprecation, missing classical instance, instance-path mismatch in the final
    step); `PocketRegion` (unused `hE`); `BridgeDoublingRun` (the `by` block inside `⟨…⟩` parsed as a two-target
    `cases`, `simp` not reducing nested option constructors, `Perm.apply_symm_apply` spelled for `Equiv`).
- Step module written (`ClosedWalkEnclosedBridgeDoublingStep`, attic 832396b7d):
  - `newFaces = insert digon (faces.map faceImage)`;
  - `mem_iff_image`, `chain_image`, `closes_image`, `bridgeCount_image_lt`;
  - `enclosedFaceSetSucc_diagram`/`_spurDiagram` with their word and cell-count equalities.
- Split with ms-compress-2, assigned by main to help on `EnclosedBridgeDoublingSuccStatement`: it takes the island
  exterior-doubling model and the induction (`ClosedWalkEnclosedBridgeDoublingProof`); this lane keeps Run and Step and
  released the unwritten `ClosedWalkEnclosedBridgeDoubling.lean` claim.
- 08:2x resume (main): this lane owns the Succ enclosed route, w1-binder-8's residual 5 (d3281c3b9, which consumes
  `ClosedWalkEnclosedSubdiagramSuccStatement` and `EnclosedSubdiagramLoopCutSuccStatement`), and
  `SameCellPocketLoopCutStatement` with the doubling, since ms-compress-2 is paused. ms-compress-2 left
  `ClosedWalkEnclosedBridgeDoublingModel.lean` on disk, never probed.
- ~08:3x OUTAGE: the laptop reboot wiped `/private/tmp`, including all nm infra (probe, land and wire scripts, lane
  records, `landed.log`, the wire queue) and this lane's backup copies. Main ruled: author offline only; no probe, land or
  infra recreation.
  - Drafts kept in the working tree, all unprobed: `ClosedWalkEnclosedOutOfOrderModel`, `ClosedWalkEnclosedPocketRegion`,
    `ClosedWalkEnclosedBridgeDoublingRun`, `ClosedWalkEnclosedBridgeDoublingStep`, and the new
    `ClosedWalkEnclosedBridgeDoublingProof`.
  - The last attic copies on origin are older than the fixes: d47ea5766 (Run), 832396b7d (Step), b662b0b9f (earlier
    fixes).
- ~08:4x written offline: `ClosedWalkEnclosedBridgeDoublingProof`.
  - Side selection `exists_bridge_side`: when both a bridge dart and its reverse bound monogons, connectivity makes the
    map those two darts, so no face is enclosed.
  - `exists_index_eq_dart`; `cellCorrespondence_map`, the cells in order with their words and enclosure.
  - `DoublingOutput` / `doublingOutput`, strong induction on `bridgeCount` over Step's two thickenings with
    `OEquivalentDiscDiagram.trans`.
  - `enclosedBridgeDoublingSucc`, and closed `enclosedLeastAreaFilterSucc` (via `enclosedLeastAreaFilterSucc_of_doubling`).
- ~08:5x INFRA READY at `$NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/f907d0cb-17e5-443b-a723-7114e9553db6/scratchpad/nm`;
  all green records were lost. `.files` is re-registered with the unlanded modules; co-probe 15 (the out-of-order model,
  the pocket region, Run, Step) is running.
- main returned `EnclosedBridgeDoublingSuccStatement` to ms-compress-2 (resumed). It overwrote the Proof draft with its
  own induction (`one_lt_faceBoundary_length_of_bridge` from `turn_next`, no `faces.Nonempty`;
  `exists_bridgeFree_of_bridgeCount_le`), without the cell correspondence. That module is ms-compress-2's.
- Written: `ClosedWalkEnclosedSubdiagramSuccProof` (attic copy).
  - `PocketRegion.diagram_cell_face_mem`, through the choice in `exists_relatorCells_of_planar`.
  - `PocketRegion.exists_cell_of_diagram_cell`, `PocketRegion.exists_cellEmbedding`.
  - The named `EnclosedBridgeDoublingCellsSuccStatement`: the doubling with cell correspondence, no `faces.Nonempty`.
  - `closedWalkEnclosedSubdiagramSucc_of_doublingCells : ... → ClosedWalkEnclosedSubdiagramSuccStatement`.
- 08:32 co-probe 0914-083214-37350 (a real rebuild, with BUILT lines): the out-of-order model, the pocket region and Run
  BUILT → **LANDED bdc97c0ae** (queued).
  - `ClosedWalkEnclosedOutOfOrderModel.not_enclosedLeastAreaFilterStatement`: the membership-form filter is refuted
    on origin, with `not_enclosedFaceSetSucc`.
  - `EnclosedPocketRegion.enclosedPocketRegionSucc : EnclosedPocketRegionSuccStatement`,
    `length_filter_le_of_bridgeFree`, `enclosedLeastAreaFilterSucc_of_doubling`.
  - `EnclosedBridgeDoubling.image`, `firstKept_lift`, `walkKeep_image_iff`, `turn_next_image`.
- Step red, because the image walk's dart type `EdgeInsertion.Dart M` equals the doubled map's `Dart` only up to
  unfolding, so `rw` and `simp` cannot match across the two.
  - Rewritten with term-mode equalities (`congrArg … .mpr`, `lt_of_eq_of_lt`); the word lemma by induction with
    definitional cons steps; `Equiv.symm_apply_apply`; `faceOf (some none)`.
  - Co-probe 0914-084224-29304 RED on the last spellings:
    - `List.isChain_map` takes the map explicitly.
    - `bridgeCount_image_lt` restated its filter predicate. The restatement picked `Option.instBEq`, but the goal
      carries `instBEqOfDecidableEq`. It now goes through the instance-generic `length_filter_lt_of_imp`.
    - In SuccProof: a `rw … at` on a `toFinset` membership, two bound proofs, and the least-area clause.
- 08:55 co-probe 0914-085500-37802 GREEN (both BUILT) → **LANDED da17060f7** (queued):
  - `ClosedWalkEnclosedBridgeDoublingStep`.
  - `ClosedWalkEnclosedSubdiagramSuccProof`: `EnclosedBridgeDoublingCellsSuccStatement` and
    `closedWalkEnclosedSubdiagramSucc_of_doublingCells`.
  - Names sent under the ruled splits: Step to ms-compress-2 (its induction); the cells statement to w1-binder-8 (its
    producer and endpoint).
- ms-compress-2 had overwritten the Proof draft by mistake; it restored this lane's backup bytes and adopted the draft
  unchanged (keeping `DoublingOutput`). It probes and lands the draft once Step is on origin.
- Earlier plan (superseded): the Ξ producer.
  - Ξ = `PocketRegion.diagram` on the doubled copy. The embedding clause needs the cells of `ofPlanar` through
    `exists_relatorCells_of_planar`'s choice, composed with the doubling correspondence.
  - The empty face set needs a cell-free disc.
- Then the Succ loop cut, over named collar and transport pieces.
- ms-compress-2 routed `SameCellPocketLoopCutStatement`: the far component of a same-face bridge dart of a cell, with
  another cell on the far side, gives an `OsinLoopCut`. Replied that no respell is needed.
  - Route: the pocket walk is `EnclosedFaceSetSucc`; Ξ is the far component via `ofPlanar`; least area from the
    bridge-free filter or the doubling; sections from `ofTwoPartBoundary` at `g = []`.
  - Open: `EnclosedBridgeDoublingSuccStatement` and an enclosed cell transport.
- ~09:0x ms-compress-2 landed `enclosedBridgeDoublingSucc`, `enclosedLeastAreaFilterSucc` and `doublingOutputSucc`
  (c2fa6eed0). w1-binder-8 closes `EnclosedBridgeDoublingCellsSuccStatement` and the Ξ endpoint over them. Main moved
  `SameCellPocketLoopCutStatement` to ms-compress-2 (label-free route over `OsinLoopCut.ofPocketRegion` with an empty
  side). This lane keeps `EnclosedSubdiagramLoopCutSuccStatement`.
- The Succ loop cut, re-read on origin:
  - `GeodesicCollar.StripStep.geodesicCollarStatement_holds` is `#audit_closed_axioms`, and `pocketCellTransport`
    is proved. So `nonempty_osinLoopCut_of_pocketRegion` needs only a pocket region with both cycles following their
    boundaries. Together those force a simple complement cycle (`PocketRegion.isSimpleClosedWalk_invDarts_outer`).
  - `enclosedPocketRegionSucc` gives only the outer one. A doubled walk can still be pinched.
  - `_twoArcs` gives `OsinMultipleEdgeCut`, not `OsinLoopCut`. The only `OsinLoopCut` producers are
    `ofTwoPartBoundary`, `ofPocketRegion` and `nonempty_osinLoopCut_of_pocketRegion`.
  - The landed pinches (`CellPocketFaceSet`, `PocketFaceSet`) forget positions in their existential wrappers, but
    their steps are concrete: `faceEdgeDoublingInside` and `pinchSplitInside` map the sides through the embedding (or
    keep them) and the arcs by `mapTo`. `CellPocketFaceSet` also needs positive arcs; `PocketFaceSet` does not.
  - Relator words longer than one letter are the landed pinch's hypothesis. Osin's condition gives it at `2 ≤ ρ`
    (`long`). At `ρ ≤ 1` a monogon relator corner has no edge to double. Hence the additive `…Long` statement.
- Route for (B), the unpinch:
  - Encode the pocket as a `PocketFaceSet` at `eps' = max ‖s‖ |s|`: `firstSide = s`, `sourceArc = A`, empty second
    side, and an empty target arc at `lo = hi = 0`.
  - Rerun `exists_goodCorners` and `exists_simple_of_firstTurns`, carrying `secondSide = []` and the word of
    `firstSide`.
  - Finish with `ofSimpleClosedWalk`.
- Route for (A): the bridge-count induction over Step, carrying a side and an arc. ms-compress-2's A2 makes public
  `EnclosedBridgeDoubling.darts_map_image_cellArc` and `darts_map_image_cellArc_spur`, to be imported here, not
  re-derived.
- 09:21 probe 0914-092142-71842 GREEN (BUILT): `Estimating/OsinEnclosedSubdiagramLoopCutSuccProof`, landing with this
  report:
  - `EnclosedBridgeDoublingSideArcSuccStatement`, `EnclosedLoopPocketUnpinchSuccStatement`;
  - `EnclosedLoopPocketRegionSuccStatement`, `enclosedLoopPocketRegionSucc_of_pieces`;
  - `EnclosedSubdiagramLoopCutSuccLongStatement`, `enclosedSubdiagramLoopCutSuccLong_of_pocketRegion`,
    `enclosedSubdiagramLoopCutSuccLong_of_loopCutSucc`;
  - `one_lt_length_of_two_le_rho`.
  - Claimed next: `Estimating/OsinEnclosedLoopPocketUnpinch.lean` (B) and `ClosedWalkEnclosedBridgeDoublingSideArc.lean`
    (A).
- ~09:36 API/DNS outage. Reconciled on resume:
  - da17060f7 and 372f6a714 are on origin with matching bytes and are in `landed.log`.
  - The in-flight unpinch probe 0914-093234-44793 died on the MSI hop (rc=255) and compiled nothing.
  - The MSI master is back.
- (B) closed. 10:07 probe 0914-100759-40690 GREEN (BUILT), landing with this report:
  `enclosedLoopPocketUnpinchSucc : EnclosedLoopPocketUnpinchSuccStatement`, `PocketFaceSet.ReadsSide` and its two step
  lemmas, `exists_goodCorners_readsSide`, `exists_simple_of_firstTurns_readsSide`, `EnclosedLoopPocket.pocketFaceSet` and
  `pocketFaceSet_firstTurns`, and `enclosedSubdiagramLoopCutSuccLong_of_doubling`.
- Interface note (not a false printed claim): the Long form needs relator words longer than one letter.
  - Binder 3's consumers choose their own ρ threshold (`max 1 rho1` in the X-pocket and in
    `osinLemma94CaseOneRCellSpur_of_enclosure`), so a `max 2 rho1` copy loses nothing.
  - Additive module `Estimating/OsinLemma94SameCellEnclosedSuccLong`: the X/Y pockets, the spur branch and binder 3
    over `EnclosedSubdiagramLoopCutSuccLongStatement`, and binder 3 from the side-and-arc doubling. Probe after the
    unpinch lands.
- Remaining leaf: (A) `EnclosedBridgeDoublingSideArcSuccStatement`, by the bridge-count induction over Step.
  - The walk splits as `A.darts ++ invDarts s`, and the image side is `invDarts X' ((invDarts X s).map image)`.
  - Its word comes from `dartWord_invDarts_diagram` / `_spurDiagram` at `invDarts s`.
  - The arc comes from ms-compress-2's `darts_map_image_cellArc` / `_spur` (A2, not yet on origin).

## Progress log

- 17:16: ledger landed (677b7cf09).
- 17:17: probe 0913-171711-24588 GREEN. All three modules BUILT and COMPILED, with `#audit_closed_axioms` and `#audit_axioms`
  in each module. The lead restart killed the local waiter, so no record was written. The re-probe 0913-172928-65828 was
  GREEN, restoring the same md5s from the cache, and wrote the record. Attic copies f9af58705.
- 17:3x: **G1–G5 CLOSED, LANDED b593627ca** (wire queued: AmenableExtensionPrintedSteps, CliffordDefectCommutatorSentence,
  VerticalAscendingHNN).
  - G1 `VerticalAscendingHNN.verticalEquivHNN : Vertical α hα ≃* HNNExtension Γ ⊤ α.range (ascendingIso α hα)`, sending
    `t ↦ t` and `ι γ ↦ of γ`; closed endpoint `manuscriptPrintedVerticalIsAscendingHNN`; plus
    `manuscriptSentence_telescopeIsUnionOfConjugates`: `range inl = ⋃ₙ {t⁻ⁿ ι(γ) tⁿ}`.
  - G2 `AmenableExtensionPrintedSteps.manuscriptSentence_traceIsFixedPointRatio`, `..._traceCaseMovesFolnerCoordinate`
    (ḡ ≠ 1) and `..._traceCaseFibre` (ḡ = 1: `b(g,x) = σ(x)⁻¹gσ(x) ≠ 1` and `θ(b(g,x))q ≠ q`).
  - G3 `..._defectIsBoundaryCompression` (the entrywise identity) and `..._printedHSDisplay`
    (`‖·‖₂² ≤ |boundary F h̄| / |F|`).
  - G4 `CliffordDefectCommutatorSentence.manuscriptSentence_defectContainsCommutatorSquaringToCentralInvolution` and
    `..._finiteCentralSubgroupInDefect`.
  - G5 `AmenableExtensionPrintedSteps.manuscriptSentence_translationFormula`.
  - Census rows landed with this report: `metadata/nm-census-rows/ms-traces-2.tsv` (8e53d32e3fb8 regraded from structural
    to formalized; d5c52ca23af0, da2fd300384a, 89bc31ec5034 and 1ea7f92c66a1 gain the new carriers; dc43ec6b23ed and
    5306701b688c name existing carriers they omitted).
- Range state: every sentence of tex 1859–1976 is carried by a closed declaration along the printed route, or is honestly
  `structural` (d47b613bb096, 4cbf47e489a6) or a `definition`. The new carriers become root-reachable once root-wire
  wires b593627ca.
- 19:15 (item 2): A, B and C written; claim landed 6017fd1a7, attic copies 782b0019f; probe 0913-191818-69417 running.
  - A `ClosedWalkEnclosedSubdiagram`: `EnclosedFaceSet Δ faces outerWalk` (the outside walk lists the reverses of the
    boundary darts of `faces` plus bridge darts both ways; closed dart walk; the turning condition of
    `IsNoncrossingClosedWalk` without `alpha_not_mem`); `ClosedWalkEnclosedSubdiagramStatement` (∃ Ξ reading
    `invDarts outerWalk`, at most the enclosed cells, a cell when the set holds one, a word-preserving index
    embedding, least area inherited); `enclosedSubdiagram_leastAreaCut`.
  - B `Estimating/OsinEnclosedSubdiagramLoopCut`: `EnclosedSubdiagramLoopCutStatement`, the hypotheses of
    `nonempty_osinLoopCut_of_pocketRegion` over an enclosed face set. It is the Prop ms-intro-1's
    `OsinLemma94CaseOneIslandStatement` reduction consumes.
  - C `ClosedWalkIslandModel`: six darts, relator loops Π and I, bridge t. The pocket walk `[2,4,3,0]` is a closed dart
    walk and not simple; `{Π, I}` shares no edge; `EnclosedFaceSet diagram {Π, I} [1,2,5,3]`; calibration: the clauses
    of the construction statement hold, realized by the diagram itself.
- 19:20: ms-intro-1's audit. `DiscDiagram.ofPlanar` (+ `ofPlanar_boundaryWord`, `ofPlanar_rCellCount`),
  `exists_relatorCells_of_planar` and the proofs of `PocketRegion.diagram_rCellCount_pos` and `_lt` supply Ξ and its
  counts over a planar map along the walk. w1-binder-2 is building that map (`BridgeComponentMap`, the far component of
  an edge deletion). The missing piece is least area: `length_filter_mem_le` needs `IsDiscRegion`. Named in A as
  `EnclosedLeastAreaFilterStatement`, with `leastArea_of_enclosedLeastAreaFilter` giving the least-area clause from it.
  `InnerDiscRegion` and the zero-cell merge do not apply (they need disc regions or FollowsBoundary).
- 19:28 probe 0913-191818-69417: A and B BUILT; C red (three elaboration errors). 19:40 co-probe 0913-194037-12185: A
  and B BUILT again at their current bytes, C red (two `simpa` steps compared `diagram.toCombMap` terms with `M` terms
  at reducible transparency; replaced by `exact`).
- **A and B LANDED a5dc9e6b0** (wire queued): `ClosedWalkEnclosedSubdiagram` (`EnclosedFaceSet`,
  `ClosedWalkEnclosedSubdiagramStatement`, `enclosedSubdiagram_leastAreaCut`, `EnclosedLeastAreaFilterStatement`,
  `leastArea_of_enclosedLeastAreaFilter`) and `Estimating/OsinEnclosedSubdiagramLoopCut`
  (`EnclosedSubdiagramLoopCutStatement`).
- 19:45: C re-probing alone (0913-194445-40364). B gains `twoPartSectionCuts`, `twoPartSectionCuts_count`,
  `twoPartSectionCuts_side_short` and `OsinLoopCut.ofTwoPartBoundary`, the loop cut from any least-area diagram whose
  boundary word is a short quasi-geodesic side followed by a quasi-geodesic arc (attic copy 66d2418a6; probe after C).
- Sent w1-binder-2 the landed names (its shared-construction proposal: `BridgeComponentMap`, the far component of a
  same-face bridge). For binder 2's pocket the far side is Ξ itself. For binder 3's island, deleting t isolates only the
  island, so the component serves `EnclosedLeastAreaFilterStatement` rather than Ξ.
- **C LANDED 690bf92f2** (probe 0913-194445-40364 GREEN, BUILT; wire queued): `ClosedWalkIslandModel` (`planar`,
  `diagram`, `pocketWalk_isClosedDartWalk`, `pocketWalk_not_isSimpleClosedWalk`, `invDarts_outerWalk`,
  `islandFaces_no_common_edge`, `enclosedFaceSet`, `enclosedSubdiagram_realized`).
- **B's two-part loop cut LANDED e783c654c** (probe 0913-195515-81283 GREEN, BUILT; the module was already queued):
  `twoPartSectionCuts`, `twoPartSectionCuts_count`, `twoPartSectionCuts_side_short`, `OsinLoopCut.ofTwoPartBoundary`.
- 20:15 resume after the API outage. The next item from main: this lane owns `EnclosedLeastAreaFilterStatement`, with
  ms-inverses-1 helping by agreement; binder 3's enclosed route and w1-binder-6's Γ₁ carrier need it.
- Heads-up from main (~19:55): w1-binder-6 builds the singular Γ₁ carrier for a full t₁ on the `EnclosedFaceSet`
  modules; ms-inverses-1 may consume the loop cut for its excision rest.
- Residual Props of item 2 (unowned producers): `ClosedWalkEnclosedSubdiagramStatement` (construction over a planar map
  along the walk; w1-binder-2's component map covers the far-side case), `EnclosedLeastAreaFilterStatement` (singular
  least-area bound), and the transport of regions to the arc (named once the component map lands).
