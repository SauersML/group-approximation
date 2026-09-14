# Lane ms-binary: "The binary example" and the opening of "MF quotients of unit groups"

Range: tex 1175–1231 at origin/main 68481e4d7. Snapshot: origin/main 61363f1b9 (2026-09-13). Census rows were matched by
text, because the census line numbers (1163–1205) are at the pre-chain-core manuscript hash.

Every sentence of the range has a census row. Every literature input the range uses is proved on main, not assumed:
- Khanh–Thanh Proposition 4.2 and Corollary 4.4;
- Ershov–Jaikin-Zapirain Theorem 1.1;
- Bekka–de la Harpe–Valette Theorem 1.3.1;
- Abrams–Aranda;
- Ara's exchange theorem;
- Preusser Theorem 3;
- Aranda–Crow Corollary 4.3;
- Whitehead's lemma.

Tex line 87 defines MF only for countable groups, so `IsCDEOperatorMF M` with `[Countable M]` is the printed generality.

## Ledger

| key | status | sentence | verdict |
|---|---|---|---|
| 2ff180315a15 | definition | Put R = L_{F_2}(1,2) and H = R^×. | OK: `RankFourEndpoint.R`, `BinaryExampleUnitGroup` |
| 98115b8e2580 | formalized | the right-module maps R ≅ R ⊕ R, and H ≅ GL_4(R) = EL_4(R) [KhanhThanh] | OK: `manuscriptSentence_leavittModuleEquivProd` (inverse maps, additive, right linear); `manuscriptSentence_unitsEquivGLFourEqELFour` (GL_4(R) ≅ R^× by the prefix code; EL_4 = ⊤ via `BinaryLeavitt.elementaryGroup_eq_top`, proved from `glTwo_eq_elementary_holds`) |
| cbb223c4d600 | structural | We identify H with EL_4(R). | OK: `unitsEquivHeadline` |
| a71f65809e0b | formalized | relations; R satisfies the hypothesis of thm:full-defect-ring; MF homomorphisms trivial; R f.g. ⇒ (T) [EJZ] ⇒ f.g. [BHV] | ROUTE GAP (see below). EJZ is `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` and BHV is `KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`; both are OK |
| e47b80780566 | formalized | Since e_{12}(1) ≠ 1, H is nontrivial. | OK |
| 2a57c4750c2a | structural | Let N be a normal subgroup of H. | OK |
| 2bf4b5aca1b4 | formalized | purely infinite simple [AbramsAranda], therefore exchange [AraExchange], so the sandwich [Preusser, Thm 3] | OK: the AGP idempotent form, `isExchangeRing_of_isPurelyInfiniteSimpleRing`, `preusser_sandwich_of_isExchangeRing` and `manuscriptSentence_rankFourSandwich` (Preusser Propositions 20 and 21 proved) |
| e4440282ed35 | definition | EL_4(R,I) and C_4(R,I) | OK: `relativeElementary`, `congruenceSubgroup` |
| 7a20735318a1 | formalized | R simple: I = R or I = 0 | OK |
| 9085fad2968e | formalized | commuting with e_ij(1) forces a scalar; with e_ij(a), a central scalar | OK |
| d38df1795c78 | formalized | λ ∈ Z(R) = F_2 [ArandaCrow], N = 1 | OK: `BinaryLeavitt.center_eq_bot`, `central_units_trivial` |
| bfd4d3ceba5a | formalized | So H is simple. | OK: the printed route is assembled by `PreusserAssembly.isSimpleGroup_elementaryGroup_binaryLeavitt_via_preusser` |
| 8ed259b70c4a | formalized | nontrivial, every MF hom trivial, so H is not MF | ROUTE NOTE (see below) |
| ecb74cabf11a | formalized | since R ≠ 0 satisfies the hypothesis, cor:one-sided-ring-maximal gives the C*_r and C*_max clauses | ROUTE GAP (see below) |
| a621da4b1382 | structural | All rings unital and associative. | OK |
| c0fe92a1903d | definition | equivalent and infinite idempotents; purely infinite [AGP, Def 1.2] | OK |
| 4fb6ccd3e134 | formalized | L_k(1,d) purely infinite simple [AbramsAranda] | OK: `AryLeavitt.isPurelyInfiniteSimpleRing`, for every field k and every d ≥ 2 |
| 8fdc908a49c7 | definition | GL(R), EL(R), EL(R) normal by Whitehead's lemma, K_1(R) | OK: the instance proof carries Whitehead |
| 1f5ca4f92217 | definition | κ : R^× → K_1(R) | OK |

## Gaps found

1. a71f65809e0b: the MF-homomorphism clause is proved from `rankFour_actualCoronaMFResidual_eq_top`, a rank-four
   configuration argument. It is not proved by applying thm:full-defect-ring to R, and no declaration states that R
   satisfies the printed hypothesis: ts = 1 and 1 − st full, with s = s_0 and t = t_0, witnessed by t_1(1 − s_0t_0)s_1 = 1.
2. 8ed259b70c4a: "so H is not MF" comes from `not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top`. The printed inference
   is nontrivial plus every MF homomorphism trivial, applied to the identity map.
3. ecb74cabf11a: the carriers are `ReducedCStarConsequenceRankFour`, a generic countable-group fact plus ¬MF, and
   `MaximalCStarNotFiniteRankFour`, which uses prop:max-infinite directly. The latter is in projection form plus
   ¬Dedekind-finite, so the printed proper isometry `star v * v = 1 ∧ ¬ IsUnit v` never appears. Neither applies
   cor:one-sided-ring-maximal to R.

## CLAIM

CLAIM binary-example printed-route carriers GroupApproximation/Manuscript/NonMFSentences/BinaryExamplePrintedRoute.lean

The module will state and prove:
- the printed hypothesis of thm:full-defect-ring at R;
- the MF-homomorphism clause, by the closed thm:full-defect-ring endpoint at (R, s_0, t_0, n = 4);
- "not MF" by the printed inference;
- the C* clauses, by the closed cor:one-sided-ring-maximal endpoint at n = 4, with the literal proper isometry.

## Progress log

- 2026-09-13: ledger landed at 3afadab54; printed-route module claimed.
- 2026-09-13: `BinaryExamplePrintedRoute` LANDED at eb25dd606. Probe 0913-171216-1123 was GREEN with a BUILT line, and the
  in-flight copy was preserved in the attic at be7dc5724. It adds four closed endpoints, each with `#audit_closed_axioms`:
  - `binaryExampleFullDefectHypothesis`
  - `binaryExampleTrivialMFHomomorphisms`
  - `binaryExampleNotMF`
  - `binaryExampleCStarClauses`

  The three gaps above now have printed-route carriers. Rows for a71f65809e0b, 8ed259b70c4a and ecb74cabf11a are in
  `metadata/nm-census-rows/ms-binary.tsv`. The module is queued for wiring.
- Range status: every sentence of tex 1175–1231 is carried by a closed declaration along the printed route or honestly
  classified. Nothing is open in this range.

## Binder 6 help: `CopyClean.cell_self` (main's item, 2026-09-13 ~17:45)

`OsinSectionPocketFaceSetSectionStatement` needs an O-equivalent copy satisfying `PocketWalk.CopyClean`. The fields are
split as follows; w1-binder-6's split was agreed with ms-cite-2 at 17:3x.

| field | owner |
|---|---|
| `spur` | hs-vanishes, `outerSpurThickening` |
| `cell_outer` | w1-binder-6, `SurgeryOuterCellThickening` (538fe1b33) |
| `side_cell` | ms-cite-2, `SurgeryCellSideThickening` and the side-dart doubling transport |
| `side_outer` | w1-binder-6, after ms-cite-2's transport lands |
| `cell_self` | **this lane** (below). Proposed to w1-binder-6 in one message, ~17:50 |
| `regions` | unowned; it needs ms-cite-2's side-dart transport |

Ownership check (~17:50):
- No self-edge or `cell_self` producer exists on origin, in the shared tree, in any `lanes/*.files`, or in `landed.log`.
- kh-cckw's `SurgeryHairOpening` (557195fb6) opens one hair of an inner face. Its in-flight `SurgeryHairOpeningUnbound`
  carries the unbound sum across one opening. Neither iterates to a copy without relator hairs. This lane consumes their
  names and never edits their files.
- `cell_self` and `regions` were ruled to leavitt-units at 14:00 as copies (b)/(c). Nothing has been in flight since.

CLAIM inner cell-hair thickening GroupApproximation/GGT/VanKampen/SurgeryCellHairThickening.lean

The module will state and prove:
- `IsCellHair Delta x`: a hair (`HairOpening.IsHair`) whose face is a relator cell.
- `CellHairThickeningStatement`: a distinguished section family over a diagram with no outer spur, no outer cell dart and
  no relator word of value one has a distinguished family over the same cuts on an O-equivalent diagram with the same
  three properties and no cell hair. The regions correspond with the same weight, target profiles and source indices.
  This composes after `OuterCellThickening.outerCellThickening`.
- `cell_self_of_noCellHair`: gives `CopyClean.cell_self`.
- Route: the inner doubling of `HairOpening.sectionFamily` along a cell hair. No region contains a relator cell, so
  `havoid` holds. The exterior traversal is unchanged, so no outer spur or outer cell dart appears. The number of cell
  hairs drops by one. Induct on that number.

### LANDED 6ef3e9bd9: `GGT/VanKampen/SurgeryCellHairThickening.lean`

Probe 0913-181336-30630 was GREEN with a BUILT line. It is unwired and queued for wiring. Namespace
`GroupApproximation.GGT.VanKampen.CellHairThickening`. Consume these names; they are stable.

| declaration | content |
|---|---|
| `IsCellHair Delta x` | `HairOpening.IsHair Delta x ∧ ∃ C ∈ relatorCells, C.face = faceOf x` |
| `cell_self_of_noCellHair hno i` | `CopyClean.cell_self` for the source cell `i` |
| `relatorFace_not_mem hvalue hC a` | with no relator word of value one, no region contains a relator face |
| `faceOf_none`, `faceOf_embed_dart`, `faceOf_embed`, `exists_of_faceOf_eq_keep`, `exists_of_faceOf_eq_cellFace`, `exists_of_faceOf_eq_outer` | faces of the darts of an inner `FaceEdgeDoubling.diagram` |
| `exists_of_isCellHair`, `cellHairCount_lt` | the count drops |
| `noOuterSpur`, `noOuterCellDart`, `relatorValue_ne_one` | preserved by an inner doubling |
| `exists_cellHairFree` | the induction |
| `CellHairThickeningStatement`, `cellHairThickening` (closed) | from no outer spur, no outer cell dart and no relator word of value one: `∃ S' e`, O-equivalent, keeping all three, no cell hair, same weight, profiles and sources |
| `OuterCellHairThickeningStatement`, `outerCellHairThickening` (closed) | composed after `OuterCellThickening.outerCellThickening`, from `1 < boundaryWord.length` and the value condition |

Rejected route: after rewriting with `FaceEdgeDoubling.boundary_kept`, `rw [List.mem_map]` fails. The list's element type
is `EdgeInsertion.Dart M`, while the membership instance expects `(FaceEdgeDoubling.map …).Dart`, and they agree only by
unfolding `toCombMap`. Use `List.mem_map.mp`.

### Interface request from w1-binder-6 (~18:05), accepted

The composition order is `outerSideThickening`, then ms-cite-2's cell-side thickening, then `cell_self` last. This
lane's statement will take and return:
- `1 < boundaryWord.length`;
- the value condition;
- no outer spur;
- no outer cell dart;
- `∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x`;
- `∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x`.

- In flight: `GGT/VanKampen/SurgeryCellHairThickeningSides.lean`, with `length_faceImage`, `exists_of_mem_sides` and
  `noCellSideDart`. Opening a relator face along a dart creates no cell-side dart.
- Next: `noOuterSideDart` and the six-condition induction, once `SurgeryOuterSideThickening` is on origin.
- Deviation: the uncompiled `SurgeryCellHairThickeningSides.lean` was preserved with `NM_UNVERIFIED=1` at 2d79b9a51.
  The wave-2 rules require `NM_ATTIC=1` for in-flight Lean. The module is unwired and nothing imports it, so no root
  build is affected. It is re-landed normally after a green probe, or after the fix if the probe is red.
- Repaired: probe 0913-181724-64428 was GREEN with BUILT `SurgeryCellHairThickeningSides` (5002 jobs). The probe base was
  2d79b9a51, and the blob on main (abd7ed4ce) is the blob that built, so the bytes on main are verified. The normal
  re-land had nothing to write. The module adds:
  - `length_faceImage`: the image of a face has as many darts as the face;
  - `exists_of_mem_sides`: a transported side dart is `embed` of an old side dart;
  - `noCellSideDart`: opening a relator face along a dart creates no cell-side dart.
- The six-condition draft (`noOuterSideDart`, `exists_cellHairFree_sides`, `CellHairSidesThickeningStatement`) is written
  and waits for `SurgeryOuterSideThickening` on origin.

### LANDED a36060868: `GGT/VanKampen/SurgeryCellHairThickeningSix.lean`

- Probe 0913-182155-4625 was GREEN with BUILT (5034 jobs), over w1-binder-6's `SurgeryOuterSideThickening` (acd63f3bb).
  The attic copy is 0e6326bc0. The module is unwired and queued for wiring.
- It keeps `SurgeryCellHairThickening`'s namespace, `GroupApproximation.GGT.VanKampen.CellHairThickening`, and adds:
  - `noOuterSideDart family havoid hfree`: opening a relator face along a dart creates no outer side dart.
  - `exists_cellHairFree_sides S hvalue hspur hcell hoside hcside`: the cell hair induction, keeping all five conditions.
  - `CellHairSidesThickeningStatement` and `cellHairSidesThickening` (closed, `#audit_closed_axioms`). This is the last
    step of the agreed order.
- **Takes:**
  - `1 < Delta.boundaryWord.length`;
  - the value condition;
  - no outer spur;
  - no outer cell dart;
  - `∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x`;
  - `∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x`.
- **Returns** `∃ S' e`:
  - O-equivalent to `S`;
  - the value condition;
  - no outer spur, no outer cell dart, no outer side dart and no cell-side dart;
  - no cell hair (`IsCellHair`);
  - the same weight;
  - `SameTargetProfile` and the source index for every region.
- The `CopyClean` fields then follow from `spur_of_noOuterSpur`, `cell_outer_of_noOuterCellDart`,
  `OuterSideThickening.side_outer_of_noOuterSideDart`, ms-cite-2's cell-side lemma for `side_cell`, and
  `cell_self_of_noCellHair`. `regions` is still unowned, because it needs ms-cite-2's side-dart transport.

## Binder 3, cell-pinch branch, shape (2b): the two-arc loop cut (main's item, ~18:3x)

After an innermost value-one G-lobe is excised from a pinched `∂Π` walk, the remaining pocket walk `x ++ b₁ ++ b₃` meets
`Π` along two arcs. jacobson's `nonempty_osinLoopCut_of_pocketRegion` (OsinPocketLoopCut:201) and
`false_of_pocketRegion_of_below` (OsinLemma94OneCellSameCell:367, ca94522e2) take a single `CyclicArc`.

Ownership check (~18:4x):
- Nothing named two-arc exists on origin, in the shared tree, in `lanes/*.files`, or in `landed.log`.
- ms-intro-1's `ClosedWalkLobeExcision` excises a lobe from a closed dart walk. ms-inverses-1 claimed
  `ClosedWalkInnermostLobe` and the (2b) consumer Prop. Neither builds a cut.
- jacobson's files are consumed and never edited.

Calibration finding: the cut already exists. `nonempty_osinMultipleEdgeCut_of_pocketRegion`
(OsinPocketMultipleEdgeAssembly:88) and `PocketRegion.fourSectionCuts_cellTransport` take `{i j}` with no `i ≠ j`, and
only ask that the sides have norm at most ε. A pocket whose inverse complement cycle reads `s ++ invDarts A₁ ++ invDarts A₂`,
with both arcs on the same cell `i`, is a multiple-edge cut at `j = i` and `s₂ = []`. `OsinMultipleEdgeCut.false_of_below`
refutes it with the same `3μ < 1 − 13μ` budget. A one-arc `OsinLoopCut` cannot take the pair: its section count is 2,
and a concatenation of two arcs need not be quasi-geodesic.

CLAIM two-arc pocket cut GroupApproximation/GGT/VanKampen/Estimating/OsinPocketLoopCutTwoArcs.lean

Draft, probing:
- `nonempty_osinMultipleEdgeCut_of_pocketRegion_twoArcs`: the jacobson hypotheses with `A₁ A₂ : CyclicArc (cellDarts X i)`
  and `invDarts X P.outer.cycle = s ++ invDarts X A₁.darts ++ invDarts X A₂.darts`.
- `false_of_pocketRegion_of_below_twoArcs`: the refutation below `Δ`, through `pocketCellTransport` and `o52LeastArea`.
- The names and premise shape will follow ms-inverses-1's spelling of the (2b) Prop. Nothing lands as a statement before
  that spelling arrives.

Spelling agreed with ms-inverses-1 (~18:5x):
- `false_of_pocketRegion_of_below_twoArcs` keeps every binder of `false_of_pocketRegion_of_below` verbatim, with `A`
  replaced by `A₁ A₂ : CyclicArc (cellDarts X i)` and `hdecomposition : invDarts X P.outer.cycle = s ++ invDarts X A₁.darts
  ++ invDarts X A₂.darts`. The draft already matches.
- The producer is renamed to main's name, `nonempty_osinLoopCut_of_pocketRegion_twoArcs`. Its type is
  `Nonempty (OsinMultipleEdgeCut D lambda c eps Delta)`, the four-section cut with an empty second side, because
  `OsinLoopCut.count_eq` is fixed at 2.
- In ms-inverses-1's excision, `A₁` is the `B₃` arc, `A₂` is the `B₁` arc, and `s = invDarts X`. Either arc may be empty,
  and no `0 < A.length` hypothesis is needed: the multiple-edge producer takes arbitrary arcs, and nondegeneracy comes
  from `ne_or_of_leastArea` and the relator cell inside.

### LANDED 6672828c1: `GGT/VanKampen/Estimating/OsinPocketLoopCutTwoArcs.lean`

Probe 0913-185400-52429 was GREEN with BUILT (10164 jobs). The attic copy is 8d5d4cf69. The module is unwired and queued
for wiring. It is additive: it imports `OsinLemma94OneCellSameCell` and edits no jacobson file. Namespace
`GroupApproximation.GGT.VanKampen`.

| declaration | content |
|---|---|
| `nonempty_osinLoopCut_of_pocketRegion_twoArcs` | jacobson's pocket hypotheses, with `A₁ A₂ : CyclicArc (cellDarts X i)` and `invDarts X P.outer.cycle = s ++ invDarts X A₁.darts ++ invDarts X A₂.darts`, give `Nonempty (OsinMultipleEdgeCut D lambda c eps Delta)`: `nonempty_osinMultipleEdgeCut_of_pocketRegion` at `j = i`, `s₂ = []` |
| `false_of_pocketRegion_of_below_twoArcs` | every binder of `false_of_pocketRegion_of_below` verbatim, with the two arcs: `False`, through `pocketCellTransport`, `o52LeastArea` and `OsinMultipleEdgeCut.false_of_below` |

Both carry `#audit_axioms`. No false-as-stated Prop. The (2b) budget is the multiple-edge budget already proved on main:
`μ/2 + μ + μ/2 + μ = 3μ`, against `1 − 13μ` for `μ ≤ 1/16`.

## V3 waist residual 1: `OsinLemma94ClassEndLoopsInput` (main's item, ~19:0x)

The residual is ct-bilateral-cell's, from `Estimating/OsinLemma94ClassSection` (2b2af4479). Its clauses:
- (a) `∑_{budget polygons} #otherClasses ≤ K n`;
- (b) `hside`;
- (c) `classEnd` and `regionEnd` lengths at most `B`;
- (d) `hbubble`.

**Owners' drafts (checked ~19:0x).** The owners have been down since 17:56, and nothing is left to land under their
evidence:
- sec5-sentences: every `.files` entry equals origin. The kind-transition layer is landed (`OsinLemma94ClassTransitions`,
  ec3c531fc); its residual is `OsinLemma94LongTransitionInput`.
- hull-component: the `ClassCovers` and `JunctionPocket` modules are landed and the backups match origin. The
  polygon-level bad-junction exclusion is unwritten.
- hull-count94: the planned producer of `Q`, `OsinLemma94ClassJoins`, was never written. It is not in the shared tree,
  the backups, the attic, or any green record.

**Hand model tests of (a) and (d).**
- **Model: one relator cell (`n = 1`) with many value-one lobes.** Take `r = g₁ t₁ g₂ t₂ …` with value-one triples
  `t = h h' (hh')⁻¹` over a finite `H` of order at least 3, separated by aperiodic geodesic pieces.
  - Every subword has `λ|u| − c ≤ |val u|` at lobe density up to `(1 − λ)/λ`, so quasi-geodesic relators can carry
    `Θ(|r|)` lobes.
  - The lobes are drawn as G-triangles attached inside the cell's walk.
  - Each triangle is a one-class polygon of kind `cell i`, and its three reversed darts are unbound and other-facing. No
    class of another polygon holds them, because faces are distinct, so only end loops can cover them. There are at most
    `2·#classes + 4|M|` end loops of at most `B` darts each.
- **Verdict: not a refutation.**
  - On this pinched copy the family is not globally distinguished. Un-pinching the lobes (an O-equivalence) lets a region
    to the section absorb them, and that family is heavier (`weight_maximal`).
  - On a globally distinguished family the lobe darts are bound, so (d) is vacuous there. (a) passes on the model
    because the triangles are not budget polygons.
  - So (a) and (d) hold through `weight_maximal` only together with the bubble un-pinch surgery (roster l.850, owner
    leavitt-units, gated and unbuilt). This agrees with sec5-sentences' pinched-bubble finding.
  - A Lean refutation or proof needs that surgery. It is a dependency, not a false Prop.

**Clause (b) is closed on main.** `hside` is a composition of landed lemmas in `OsinLemma94PolygonCovers`:
- `alpha_faceOf_not_cell_of_unbound`: no relator cell and no exterior across, through `weight_maximal` and a digon region;
- `exists_relatorSide_of_unbound`: the dart across lies on an (A1) side of the polygon of that face;
- the premises `hvalue` and `hlen`, from `cell_listVal_ne_one` (`c < λρ`) and `one_lt_cellDarts_length` (`1 < ρ`).

CLAIM class end-loops side clause and budget residual GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ClassEndLoopsSide.lean

The module will state and prove:
- `classEndLoops_side`: clause (b) for any globally distinguished family and realized polygons under `C(ε, μ, λ, c, ρ)`
  with `0 < λ`, `c < λρ` and `1 < ρ`.
- `OsinLemma94ClassEndLoopsBudgetInput`: the residual with clause (b) removed, so only (a), (c) and (d) remain.
- `osinLemma94ClassEndLoopsInput_of_budget`: the residual back, with `ρ₀` raised to `max ρ₀ (⌈c/λ⌉₊ + 2)`.

### LANDED 68b6b0e96: `GGT/VanKampen/Estimating/OsinLemma94ClassEndLoopsSide.lean`

Probe 0913-194233-25873 was GREEN with BUILT (10159 jobs). The attic copy is 1e9544191. The module is unwired and queued
for wiring. It imports only `OsinLemma94ClassSection`.

| declaration | content |
|---|---|
| `GloballyDistinguishedSectionFamily.classEndLoops_side S P hW hlambda hrhoc hrho` | clause (b) of `OsinLemma94ClassEndLoopsInput`, under `C(ε, μ, λ, c, ρ)` with `0 < λ`, `c < λρ` and `1 < ρ`: every dart of `S.unboundOffRegions i` not facing its own cell lies across an (A1) side of `P` |
| `OsinLemma94ClassEndLoopsBudgetInput` (residual) | the same hypotheses and conclusion without clause (b): the other-class budget, the end loops of at most `B` darts, and `hbubble` |
| `osinLemma94ClassEndLoopsInput_of_budget` | `OsinLemma94ClassEndLoopsInput` from the residual |

- Rejected route: without `open scoped Classical`, `Finset.mem_filter` on `unboundOffRegions` cannot synthesize
  `DecidablePred`, and `Finset.mem_sdiff` cannot synthesize `DecidableEq Dart`. The defining module opens that scope.
- What remains of residual 1 is `OsinLemma94ClassEndLoopsBudgetInput`:
  - (a) needs the class producer `Q` (`OsinLemma94ClassJoins`, unwritten), sec5-sentences'
    `OsinLemma94LongTransitionInput`, and the bad-junction exclusion;
  - (c) and (d) need the end-loop assignment for one-class bubbles.
  - The model tests above show that (a) and (d) are true only through `weight_maximal` together with the bubble un-pinch
    surgery (roster l.850).

## Bubble un-pinch surgery (main's item ~19:5x, resumed 20:15 after the API outage)

Roster l.850 and l.1273–1276 give the item to leavitt-units, which is down. Consumers: this lane's (a), (c) and (d), and
sec5-sentences' `OsinLemma94LongTransitionInput`, which ms-compress-1 takes.

Ownership check (20:2x):
- Nothing named un-pinch or absorption exists on origin, in the shared tree, in any `lanes/*.files`, or in `landed.log`.
- Every leavitt-units file equals origin.
- hull-respell's vertex explosion is on main as `PinchSplit`:
  - `SurgeryPinchSplit{Map,Diagram,Regions,Sections,Extremal}`;
  - `Input` is two darts at one vertex whose corners are distinct G-faces off the exterior;
  - `transportDistinguished` gives a family with the same weight, card, darts and unbound darts when every region avoids
    both faces.
- Nothing on main adjoins a region after a split.

Calibration on the lobe model:
- Take a cell `Π` with a lobe `h h' (hh')⁻¹` at `v`, enclosing a G-triangle `g`. The corners at `v` read `Π`, `g`, `Π`,
  and the outer face `f` between the two visits.
- Splitting `v` between the corners of `g` and `f` splices the walk of `g` into `f`. Where `f` read `α e_out, α e_in`, it
  now reads `α e_out, α(hh')⁻¹, α h', α h, α e_in`: the reversed arc of `Π` through the lobe.
- If `f` is unselected and reads an arc of `Π`, a short side, a target arc and a short side, the merged face is a
  region whose source arc absorbs the lobe. The family then weighs more, against `weight_maximal`.
- If the merged face is not a contiguity region, the split only merges, with the same weight (`transportDistinguished`).
- If `f` lies in a selected region, `Input.Avoids` fails, and absorbing needs a transport of that region through the
  merge, which is not on main.

CLAIM bubble un-pinch absorption GroupApproximation/GGT/VanKampen/SurgeryPinchSplitAbsorption.lean

The module will state and prove:
- `GloballyDistinguishedSectionFamily.false_of_avoided_singleton`: a legal realized family at least as heavy as `S`, with a
  singleton region at a face it avoids, with nonempty arcs and respecting the sections, contradicts maximality.
- `PinchSplit.Input.merged_noInternalFaceDart`.
- `PinchSplit.false_of_mergedRegion`, and the closed Prop `PinchSplitAbsorptionStatement` / `pinchSplitAbsorption`.

The interface and both caveats (an unselected corner that does not read as a region; a selected neighbour) went to
ms-compress-1 in one message (20:2x).

### LANDED 68ea7fe96: `GGT/VanKampen/SurgeryPinchSplitAbsorption.lean`

Probe 0913-203347-30324 was GREEN with BUILT (5012 jobs) on the first try. The claim landed at d22daa111 and the attic
copy at b1cfc0537. The module is unwired and queued for wiring. It imports `SurgeryPinchSplitExtremal` and
`Estimating/SingletonFaceRegion`.

| declaration | content |
|---|---|
| `GloballyDistinguishedSectionFamily.false_of_avoided_singleton S T hlegal hweight H havoid hrespects hsource htarget` | a legal realized family `T` with `S.weight ≤ T.weight`, carrying a singleton region `⟨{f}, H⟩` at a face no region of `T` contains, with nonempty arcs and respecting the sections: `False` |
| `PinchSplit.Input.merged_noInternalFaceDart I hno` | `NoInternalFaceDart I.diagram.toCombMap I.merged`, when no dart of `leftFace ∪ rightFace` has its reverse there |
| `PinchSplit.false_of_mergedRegion S I havoid H hrespects hsource htarget` | the absorption, for `I : PinchSplit.Input S.diagram` with every selected region avoiding both faces and `H : ContiguityGeometry D eps I.diagram {I.merged}` |
| `PinchSplit.PinchSplitAbsorptionStatement`, `PinchSplit.pinchSplitAbsorption` (closed) | the same, uniformly |

- No false Prop was found.
- Limits, stated in the module docstring:
  - a pinch face inside a selected region fails `Input.Avoids`;
  - a merged face that is not a contiguity region is only merged, with the same weight.

## Clauses (c) and (d) of `OsinLemma94ClassEndLoopsBudgetInput` (main's item 21:22): scope finding

Hand model tests (21:3x):
- **Where one-class polygons sit.** A one-class (A1) polygon is a G-face whose whole walk reads a reversed arc of one cell
  `Π`: a lobe hanging at a pinch vertex `v`. At `v` the corners read `Π`, the lobe, `Π`, and a neighbour face `X` across
  the two cell darts before and after the lobe.
- **`X` is never the exterior or a relator cell on `S`.** An unbound cell dart across either contradicts maximality
  (`alpha_faceOf_not_cell_of_unbound`). A bound one would put that face on a region's boundary cycle as an arc reverse,
  inside the region.
- **Nested lobes.** `cell_arc` lets the gap of a class be any dart list completing it to a reversed arc. So the gap across
  an outer lobe holds the darts of every lobe nested in it, and the first option of (d) covers them when `X` is a polygon
  whose class joins across the outer lobe and that has at least two classes.
- **`X` a polygon whose class does not join there.** The lobe complex sits at a class end, which `classEnd` covers.
- **`X` a selected region.** An arc cannot pass the lobe, so the complex sits at a corner or along a side of the region
  (length at most `ε`), which `regionEnd` covers.
- **(c).** A lobe complex reads a value-one subword of a relator, so it has at most `⌈(c + 2)/λ⌉₊` letters, and
  `B = (ε + 1)⌈(c + 2)/λ⌉₊` suffices.

Verdict:
- (c) and (d) look true, but only for a `Q` whose runs join the value-one lobe gaps or end at them. With `Q = ofSides`,
  (d) holds through class ends while (a) fails on a polygon carrying many lobes along one cell.
- So (d) is a property of the producer of `Q`: `OsinLemma94ClassJoins`, hull-count94's planned module, unwritten, owner
  down. It is not a consequence of the absorption.
- `pinchSplitAbsorption` enters (a), through `OsinLemma94LongTransitionInput` (ms-compress-1), not (c) or (d).
- No false Prop found. Sent to main as a blocker, with options.

## The class producer `Q` (main's ruling 23:12, option 2)

Ruling: this lane takes `OsinLemma94ClassJoins`, the producer of `Q`, with gaps and end loops together, proving (c) and
(d) of `OsinLemma94ClassEndLoopsBudgetInput`.
- Clause (a)'s long-transition count goes to ms-compress-1 (`OsinLemma94LongTransitionInput`, as declared at 013a2dc59).
  The interface arrived by message at 23:1x; no reply was needed.
- ms-inverses-3 does the bad-junction exclusion.
- ms-core-2 is not resumed, and its plan is taken from its report.

**State at origin 37551fd93 (23:16).**
- The absorption, `ClassEndLoopsSide` and `LoopCutTwoArcs` are all root-wired.
- No `ClassJoins` or `badJunctions` declaration exists on origin.
- ms-core-2 left one unlanded draft, `Estimating/OsinLemma94ClassProducerGaps.lean` (183 lines, 21:45, no green record,
  no backup, no attic copy). It holds `ClassProducer.cellGapOf`, `boundaryGapOf`, `Backward`, `isChain_append_cellGapOf`,
  `OsinLemma94RealizedPolygons.junctionGap`, `ClassJoins` and `badJunctions`.
- Its other three planned files (`ClassProducer`, `…CellArc`, `…BoundaryArc`) were never written.

**The join rule** is ms-core-2's `ClassJoins P k s`. All four conditions must hold:
- `KindJoins k s`;
- the junction gap reads a word of value one;
- a same-cell gap has no dart on the polygon face;
- a same-section junction moves forward along `∂Δ`.

The cell gap is `α (facePerm^m a), …, α (facePerm a)` along the cell from `a = α e'` to `b = α e`, with `m` least.

**Hand model tests of the join rule on the lobe models.**
- **M1, a simple lobe `h h' (hh')⁻¹` at `v`, enclosing a G-triangle `g`, with a polygon `f` along `Π` on both sides.**
  - The gap is `g`'s darts. Its value is one, and none of its darts lies on `f`, so the sides join.
  - The lobe darts lie in `f`'s class darts, and (d) holds by its first option when `f` has at least two classes.
  - (a) is not charged.
- **M2, nested lobes: a big lobe `L` containing a one-class polygon `f₀`, itself carrying a small lobe `g` at `v`.**
  - The outer polygon's gap across `L` holds the darts of `f₀` and `g`, with value one, so it joins and covers both.
  - Inside `L`, every junction of `f₀` joins, so `f₀` has one class (`exists_cyclicRuns`: count ≤ max 1 0).
- **M3, a loop of `∂Π` at `v` enclosing another relator cell `Π'`.**
  - The gap value is the product of the enclosed cell values, generally not one, so the junction is refused and counted
    in `badJunctions`.
  - The exclusion is a loop-cut kill of a pocket with a relator cell inside (`false_of_pocketRegion_of_below`, or the
    two-arc form 6672828c1), which is ms-inverses-3's item.
  - If the product happens to be one, the junction joins and `cell_arc` still holds, because the gap is a run of `Π` darts.
- **M5, a value-one pearl on `∂Δ` (a hair `x x⁻¹` or one G-face), sec5-sentences' model.** `boundaryGapOf` reads the pearl,
  with value one, moving forward, so the sides join and (a) is not charged.
- **M6, a class of a polygon that runs all around one cell.** With no gap dart on the face walk, a first dart that recurs
  would occur twice on the sides or on a gap, which is impossible. So the class is one arc of length at most
  `|cellDarts j|` (hull-count94's argument).
- **M4, a lobe or a flower of lobes at a class end next to a different kind** (short, cutting, boundary or another cell).
  - This is not a gap, so it needs an end loop.
  - The returns of `∂Π` to the end vertex read one value-one subword of the relator, of length at most
    `⌈(c + 2)/λ⌉₊`, so (c) holds for that end loop.
  - Defining `classEnd` from the rotation at the end vertex is the hard design item of this item.

Verdict: the join rule passes M1, M2, M3, M5 and M6. M4 is a design item for the end loops, not a defect of the rule.

CLAIM class producer from ClassJoins GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ClassJoins.lean
CLAIM class producer end loops GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ClassJoinsEndLoops.lean
ADOPT (credited to ms-core-2; probed and landed by this lane, file unchanged unless red)
GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ClassProducerGaps.lean

Plan:
- **`ClassProducerGaps`, adopted.** The file is unchanged unless it is red.
- **`ClassJoins` module, producer.**
  - `classPolygonsOfJoins P …`, with classes the runs of `exists_cyclicRuns` under `ClassJoins`, gaps
    `junctionGap` on joined sides and `[]` on run ends.
  - `cell_arc` and `boundary_arc` through `isChain_append_cellGapOf` and `exists_appendArc`
    (`OsinLemma94SameCellSpan`); `quasiGeodesic` from `OsinCCondition`.
  - The counts: `classCount k ≤ max 1 #¬ClassJoins`, and on polygons with at least two classes
    `#otherClasses k ≤ #short + #runEnds + #badJunctions`.
  - The residual `OsinLemma94BadJunctionInput` (`∑_{relatorPolygons} #badJunctions ≤ K n`, under the binders of
    `ClassCountInput`) is stated for ms-inverses-3.
- **`ClassJoinsEndLoops` module.** `classEnd`, `regionEnd` and clauses (c) and (d) for `classPolygonsOfJoins`.
- **Handoff.** Clause (a) for this `Q` is assembled from ms-compress-1's `osinLemma94KindTransitionInput_of_longTransitions`,
  `card_filter_not_le_kindNonJoins_add`, ms-inverses-3's bad-junction input, and ct-bilateral-cell's
  `classBudget_of_otherClasses` for the cutting classes.

Progress (23:3x):
- Claim landed at fa1f24c08. The adopted draft's attic copy is 5801a5272.
- The first probe refused, because `ms-binary.files` listed the two unwritten producer paths. They were dropped from the
  file until they are written.
- Probe 0913-233548-81701 of the adopted `ClassProducerGaps` was RED on two defects, so its bytes change. Both were fixed:
  - the theorems use `Nat.find h` without the classical scope of `cellGapOf` (57, 62, 69, 94, 95);
  - `pow_succ'` had the wrong index in `isChain_cellGapOf` (83).

Interface agreed with ms-inverses-3 (23:3x): `OsinLemma94BadJunctionInput` sums `#badJunctions` over
`P.relatorPolygons.filter (2 ≤ #¬ClassJoins)`, not over all `relatorPolygons`.
- A one-side lobe polygon has a self-junction (`(0 + 1) % 1 = 0`) whose gap is the rest of the relator, with value not
  one, so each lobe would be one bad junction and the unfiltered sum would be unbounded.
- The filter contains `Q.budgetPolygons`, since `classCount ≤ max 1 #¬ClassJoins`, so (a) loses nothing.
- ms-inverses-3's module is `Estimating/OsinLemma94BadJunctionExclusion.lean` (claimed at ddd310d78). Its value clause for
  G-face-only pockets may keep `RegionFaceAssemblyStatement` as a named binder.
