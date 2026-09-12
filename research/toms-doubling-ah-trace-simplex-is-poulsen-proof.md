---
rg: 2
id: toms-doubling-ah-trace-simplex-is-poulsen-proof
kind: route
title: Branch traces are extreme by tail concentration, and deep branches realize every empirical measure
target: toms-doubling-ah-trace-simplex-is-poulsen
requires: []
artifacts:
  - research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md
---

The proof is in Sections 2–5 of the artifact.

- **Tail concentration.** If `μ_N({x_N}) → 1` along the stages, the trace is
  extreme. A convex summand `τ'` of `τ` with weight `t` has `μ'_N ≤ μ_N / t`, and the
  dual connecting maps do not increase total variation.
- **Branch traces.** Follow the diagonal `y_{N+1} = d_N(y_N)`. Summable
  contamination makes the sequence Cauchy in total variation. Its limit is a trace
  with `‖μ_N − δ_{y_N}‖_TV ≤ 2 Σ_{s ≥ N} (1 − α_s)`, so it is extreme.
- **Density.** Fix a stage `m'` whose contamination tail is small.
  - Approximate the given trace's measure at stage `m'` by a uniform empirical
    measure on the `|L|` leaves of depth `N − m'`.
  - By (F) there is a point `y ∈ X_N` carrying those labels. Start a branch trace
    at `y`.
  - Its restriction to stage `m'` is within `4 Σ_{s ≥ m'} (1 − α_s)` of the
    empirical measure in total variation.
- **Poulsen.** Branch traces started at two distinct points differ. A nontrivial
  metrizable simplex with dense extreme points is the Poulsen simplex
  (Lindenstrauss–Olsen–Sternfeld 1978). Only density and non-closedness are used
  downstream.
- **Toms's systems.** The doubling form comes from Toms's connecting maps:
  - line-bundle summands of equal rank;
  - telescoped composites of coordinate projections;
  - point evaluations of summable normalized rank (his Proposition 4(2)).
