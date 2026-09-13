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
