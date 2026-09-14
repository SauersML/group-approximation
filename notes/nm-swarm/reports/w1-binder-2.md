# Lane w1-binder-2 — report

A second, independent start on W1 waist binder 2, `OsinLemma94UnboundSameCellStatement`
(`Estimating/OsinLemma94PolygonCount.lean:58`). Lead: session nonsofic-existence-49.

## Verdict on the binder (read only, 2026-09-13 ~17:00)

- **False as spelled.** systolic-counts' truth audit gives a hand model at `eps = 0`: `λ = 1/2`, `c = 3`, `μ = 1/16`,
  `G = ℤ/5 * ℤ/5`, `r = A·h'·x·x⁻¹·h''`. A stretch flanked by unbound darts across a cut leaves a spur dart across its
  own cell. The Prop quantifies every `eps`, with no `eps0`. audit-sec5's site 5 test (roster ruling ~14:45) agrees.
  A Lean refutation needs hyperbolicity of the free product, `OsinCCondition` at every `ρ`, weight maximality and
  `DartMinimal` lower bounds; this lane does not build it.
- The waist on origin, `relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals`, still takes `hsame`. It cannot
  be discharged as spelled until the class respell replaces binders 1–2.

## Replacement route (option (a)) and owners

| piece | state | owner |
|---|---|---|
| `OsinUnboundSameCellStretchBound`, `OsinUnboundSameCellScanBound`, `OsinUnboundSameCellNoCross` | closed | fff-periodic |
| dart-level count `OsinUnboundSameCellCount`: Σ same-cell ≤ ⌈1/λ⌉₊ Σ other + ⌈c/λ⌉₊ (n + 2 \|family\|) | planned, no file | fff-periodic |
| (C) `OsinLemma94SameCellPocketInput` | named binder | fff-periodic |
| `ClassCovers M L` | respelled (a25fe2383) | hull-count94 |
| `classCovers_of_endLoops` | red on origin since a25fe2383; queued fix `Q.ClassCovers 1 (…)` | hull-component |

## Hazard

`classCovers_of_endLoops` takes `hsameCell : Σ same-cell unbound ≤ T n`. Along an unbound stretch,
`λ X ≤ (1 − λ) N + c`, so a cell with many short pockets has `X ≈ (1/λ − 1) N`, which is not `O(n)`. With the queued
`M = 1` fix, the only cover producer keeps a hypothesis nothing can produce. The same-cell part has to be charged to the
factor on the class words.

## Claims

CLAIM classCovers_of_sameCellFactor GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ClassCoversSameCellFactor.lean

`OsinLemma94ClassPolygons.classCovers_of_sameCellFactor`: from (i) the non-self-facing unbound darts ≤ Σ S_i + L₀ n, and
(ii) Σ same-cell unbound ≤ M₀ · Σ non-self-facing + T n, conclude `Q.ClassCovers (M₀ + 1) ((M₀ + 1) L₀ + T)`. Hypothesis
(i) is what `classCovers_of_endLoops` proves once `hsameCell` is dropped; (ii) is fff-periodic's planned count with
`M₀ = ⌈1/λ⌉₊`. The module imports only `OsinLemma94PolygonClasses`, so the red cover module does not block it.

CLAIM otherFacingCover_of_endLoops GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ClassCoversOtherFacing.lean

Lead item 17:2x: a green port of hull-component's `classCovers_of_endLoops` without `hsameCell`, proving hypothesis (i)
directly in a new namespace (`OsinLemma94OtherFacingCover`), so it never collides with hull-component's module when that
one is fixed and wired.

CLAIM sameCellFactor_of_scan GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellFactorInput.lean

Ownership check 17:3x: no `OsinUnboundSameCellCount` file on origin, in the shared tree or in any `lanes/*.files` (the only
hit is the forward reference in `OsinUnboundSameCellSegments`' docstring). ko-closed's `OsinLemma94SameCellSpan` is Case 1
infrastructure (binder 3), not the site-5 count. This module states (ii) as `OsinLemma94SameCellFactorInput`
(`M₀ = ⌈1/λ⌉₊`, `T = 25 ⌈c/λ⌉₊`) and the dart-level scan residual `OsinLemma94SameCellScanInput`, and proves the
counting step `OsinLemma94SameCellScanInput → OsinLemma94SameCellFactorInput`. The scan residual is what
`OsinUnboundSameCellScanBound` gives on each cell word, with the pocket value clause `OsinLemma94SameCellPocketInput` for
the blocks. That instantiation stays with fff-periodic.

## Landed

- **`OsinLemma94ClassPolygons.classCovers_of_sameCellFactor` LANDED 2336592ee** (module
  `Estimating/OsinLemma94ClassCoversSameCellFactor`, probe 0913-170844-86401 GREEN, BUILT line checked). Closed, with no
  residual Props; `#audit_axioms` on it and on `OsinLemma94ClassCoversSameCellFactor.add_le_of_factor`. Queued for wiring.
- Consumers: the class-cover producer (hull-component's `classCovers_of_endLoops` after it drops `hsameCell`) supplies
  hypothesis (i). fff-periodic's planned `OsinUnboundSameCellCount` supplies hypothesis (ii) with `M₀ = ⌈1/λ⌉₊`.
  Composed, they give `ClassCovers (⌈1/λ⌉₊ + 1) L`, which is what `OsinLemma94ClassCountInput` asks for (`0 < M`).

- **Hypothesis (i) LANDED e3bbcf801** (module `Estimating/OsinLemma94ClassCoversOtherFacing`, probe 0913-172833-62676
  GREEN, BUILT line checked; the MSI build log shows `[propext, Classical.choice, Quot.sound]` on all nine audited
  declarations). Queued for wiring.
  - `OsinLemma94OtherFacingCover.otherFacingCover_of_endLoops`: the unbound darts whose reverse lies on a different face
    number at most `∑ S_i + (24 ε + 2 (K + 24) B) n`, from the end-loop hypotheses of hull-component's
    `classCovers_of_endLoops`, without `hsameCell`.
  - `OsinLemma94OtherFacingCover.classCovers_of_endLoops_sameCellFactor`: composed with `classCovers_of_sameCellFactor`,
    `ClassCovers (M₀ + 1) ((M₀ + 1) (24 ε + 2 (K + 24) B) + T)` from the end loops and hypothesis (ii).
  - Helper names live in `OsinLemma94OtherFacingCover`, so hull-component's module can still be wired without collisions.
    Once it is fixed, the duplicated helpers can be merged.
  - Residual premises (as in the original): `hside`, `hbubble`, the end-loop bounds `hclassEnd`/`hregionEnd` and
    `ClassBudget K`. hull-component's end-loop producers supply them.

- **Hypothesis (ii) over a named scan LANDED 95f0853ba** (module `Estimating/OsinLemma94SameCellFactorInput`, probe
  0913-173911-11662 GREEN, BUILT line checked; MSI build log: `[propext, Classical.choice, Quot.sound]` on the three
  audited declarations, no `sorryAx`). Queued for wiring.
  - `OsinLemma94SameCellFactorInput`: hypothesis (ii) of `classCovers_of_sameCellFactor` at the parameters of Lemma 9.4,
    with the Lemma 9.7(b)-below hypothesis in scope, `M₀ = ⌈1/λ⌉₊`, `T = 25 ⌈c/λ⌉₊`.
  - `OsinLemma94SameCellScanInput` (RESIDUAL): on each relator cell,
    `λ · #same_i ≤ (1 − λ) · #other_i + c · (1 + runs_i)`, with `∑ runs_i ≤ 2 |M|`. The runs bound holds because a selected
    region has one source arc and at most one cell target arc, and unbound darts are the cell's darts minus those arcs
    (`RegionPartition.unboundDarts`).
  - `osinLemma94SameCellFactorInput_of_scan`: the counting step (`le_ceil_mul_add`, `sum_le_ceil_mul_add`), with
    `S.diagram.rCellCount = Delta.rCellCount` from `S.equiv.cellIndex` and `|M| ≤ 12 n`. This reshapes (ii); it does not
    discharge the scan.
  - The scan's producer is the dart instantiation of `OsinUnboundSameCellScanBound` over `OsinLemma94SameCellPocketInput`
    (blocks from `OsinUnboundSameCellSides`), which is fff-periodic's planned `OsinUnboundSameCellCount`.

## Progress log

- 17:0x: verdict and ownership map; claim landed (7564433ff).
- 17:1x: factor cover landed (2336592ee).

CLAIM osinLemma94SameCellScanInput_of_pocket GroupApproximation/GGT/VanKampen/Estimating/OsinUnboundSameCellCount.lean (helpers OsinUnboundSameCellCycle, OsinUnboundSameCellBlocks)

Lead item 17:5x: prove the scan residual over the named premise OsinLemma94SameCellPocketInput. Ownership re-checked 18:0x: no count module on origin, in the shared tree or in lanes/*.files.

## Scan residual closed over the pocket value clause (2026-09-13 ~18:40)

- **`osinLemma94SameCellScanInput_of_pocket : OsinLemma94SameCellPocketInput → OsinLemma94SameCellScanInput` LANDED
  b6f8cb3a6** (modules `Estimating/OsinUnboundSameCellBlocks`, `Estimating/OsinUnboundSameCellCount`; probe
  0913-183240-62859 GREEN, BUILT lines checked; MSI build log: `[propext, Classical.choice, Quot.sound]` on all ten audited
  declarations, no `sorryAx`). Helper module `Estimating/OsinUnboundSameCellCycle` LANDED f99f9c6c7 (probe
  0913-181302-25319 GREEN). All three queued for wiring.
- Route, on each relator cell `i` of `S.diagram`:
  - `OsinUnboundSameCellCycle`: face-boundary positions `f^j x₀`, injective and covering; `positionCount` equals the dart
    count; a dart of a cyclic arc whose predecessor is off the arc is the arc's head.
  - `OsinUnboundSameCellBlocks.exists_base_scan`: base = an oriented same-cell dart with the longest pocket
    (`pocketLen`). Blocks join an oriented same-cell dart to its reverse: `lt_of_oriented` orders them, `false_of_cross`
    and `not_oriented_both` nest them, and `PocketValue` (the tail of `OsinLemma94SameCellPocketInput`) gives value one.
    A same-cell dart is never bound, since region faces are `G`-faces and relator words do not have value one. The closed
    `osinUnboundSameCellScanBound_holds` then gives `λ · #same ≤ (1 − λ) · #other + c · (1 + run starts)`.
  - `OsinUnboundSameCellCount`: every run start is the head of a region arc on the cell, so run starts ≤ `arcCount`
    (one per region with source `i`, one per region with target `i`), and `∑ᵢ arcCount ≤ 2 |M|`. The pocket clause applies
    to `S.diagram` through `OEquivalentDiscDiagram.leastArea` and `rCellCount_eq`; `hvalue` from
    `cell_listVal_ne_one` at `ρ ≥ ⌈c/λ⌉₊ + 2`.
- With 95f0853ba and e3bbcf801, binder 2's replacement (ii) now rests only on the named premise
  `OsinLemma94SameCellPocketInput`, which fff-periodic owns.
- 18:06 incident, recorded: my free-name check ran in parallel with the Write of `OsinUnboundSameCellCycle` and reported
  the file as taken. Checked: not on origin, in no `lanes/*.files`, not in landed.log, the attic or any backup, and the
  local mtime equals my Write. It was a race against my own file, and no peer bytes were overwritten.

CLAIM osinLemma94SameCellPocketInput GroupApproximation/GGT/VanKampen/Estimating/OsinUnboundSameCellPocketProof.lean

Lead item 18:4x: prove the (C) pocket binder `OsinLemma94SameCellPocketInput`. Its owner fff-periodic has been down since
17:56. Checked 18:4x: every file in `lanes/fff-periodic.files` equals origin, and its drafts directory holds only land
messages, probe logs and a 14:22 fragment, so there is no green unlanded draft to land under its evidence.

Hand model test of the clause:
- Spur `x x⁻¹` inside the cell: the pocket is empty (`m = 0`), so the value is 1.
- Bubble around a `G`-face `g`: the pocket reads `g`, so the value is 1.
- Relator cell in the pocket: least area plus clause (b) of Lemma 9.7 on the pocket, with fewer relator cells, gives a
  cell with contiguity degree above `1 − 13μ` to the pocket word. That word is a subword of the cell's relator, which
  contradicts the small-piece clause, or a cancelling pair against least area.
- Orientation is load-bearing. With the reverse dart oriented instead, the pocket from `d` would contain the exterior.

## Pocket clause: scope finding (2026-09-13 ~18:55), sent to main as a blocker

- Checked the kill machinery on origin. `OsinLoopCut.ofPocketRegion`, with `s = []` and `t` the pocket arc, together
  with `twoSectionCuts_cellTransport`, `o52LeastArea` and `OsinLoopCut.false_of_below` (fed by `hbelow`), kills a relator
  cell inside a pocket. It needs neither legal labels nor `GeodesicCollarStatement`. The cell-free branch follows from
  `boundary_product` on `P.diagram`.
- Both need a `PocketRegion` whose complement cycle is the arc. The only builder, `PocketRegion.ofNoncrossingClosedWalk`,
  needs `IsNoncrossingClosedWalk` (including `alpha_not_mem`), outer `FollowsBoundary`, and `reclosed_euler`.
- Gap 1: a pocket containing a nested same-cell pair violates `alpha_not_mem`, and its side is not edge-connected, so it
  has no disc region.
- Gap 2: pinched innermost pockets can fail outer `FollowsBoundary` (binder 7 territory).
- Missing: a bridge-component surgery. Delete the bridge (`CombMapEdgeDeletion`), restrict to the far component, and
  read the pocket arc as a face cycle. `isRelatorProduct_of_planar` then gives the cell-free branch; the relator branch
  also needs the component as a disc diagram and a transport that re-glues at the bridge vertex.
- Options sent to main: (a) the innermost boundary-following case over named nested and pinched residuals, (b) the
  bridge-component surgery, (c) park. I am starting (a) unless redirected.

CLAIM bridgeComponent GroupApproximation/GGT/VanKampen/BridgeComponentMap.lean (with BridgeComponentPlanar, BridgeComponentValue)

Main's ruling 19:0x: option (b), the bridge-component surgery, cell-free half first, skipping (a). The shared
construction was proposed in one combined message to ms-traces-2 and ms-intro-1:
- this lane builds the component map (edge deletion restricted to the far side, planar, with the pocket walk as a face
  cycle) and the cell-free value over `isRelatorProduct_of_planar`;
- ms-traces-2 builds the enclosed DiscDiagram, its loop cut and the transport on top of it.
