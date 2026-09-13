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

## Landed

- **`OsinLemma94ClassPolygons.classCovers_of_sameCellFactor` LANDED 2336592ee** (module
  `Estimating/OsinLemma94ClassCoversSameCellFactor`, probe 0913-170844-86401 GREEN, BUILT line checked). Closed, with no
  residual Props; `#audit_axioms` on it and on `OsinLemma94ClassCoversSameCellFactor.add_le_of_factor`. Queued for wiring.
- Consumers: the class-cover producer (hull-component's `classCovers_of_endLoops` after it drops `hsameCell`) supplies
  hypothesis (i). fff-periodic's planned `OsinUnboundSameCellCount` supplies hypothesis (ii) with `M₀ = ⌈1/λ⌉₊`.
  Composed, they give `ClassCovers (⌈1/λ⌉₊ + 1) L`, which is what `OsinLemma94ClassCountInput` asks for (`0 < M`).

## Progress log

- 17:0x: verdict and ownership map; claim landed (7564433ff).
- 17:1x: factor cover landed (2336592ee).
