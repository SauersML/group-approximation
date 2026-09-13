---
rg: 2
id: hilbert-cube-bauer-strict-comparison-divides-unit
kind: claim
title: Strict comparison divides the unit when the extreme tracial boundary is a Bauer Hilbert cube
refuted_by: [hilbert-cube-bauer-strict-comparison-indivisible-unit-exists]
distinct_from:
  strict-comparison-forces-tracially-divisible-unit: that is the nuclear crux over every trace simplex; this is the exact case over one boundary, the Hilbert cube, where every screening argument fails.
  bauer-c-space-strict-comparison-divides-unit: that proves division over boundaries with Haver's property C; the Hilbert cube lacks property C, so this lies outside that theorem.
  bauer-unit-division-metric-order-criterion: that proves a sufficient metric criterion on any boundary; this asks whether strict comparison makes the unit divide over the Hilbert cube, by that criterion or otherwise.
  r-fibre-w-star-bundles-divide-the-unit-uniformly: that asks for division in abstract bundles with no comparison hypothesis; this keeps strict comparison of a C*-algebra and fixes the base to be the Hilbert cube.
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md
---

**OPEN.** Let `A` be a unital, simple, separable, exact, non-elementary C*-algebra
with strict comparison of positive elements. Suppose `T(A)` is a Bauer simplex
whose extreme boundary `K` is homeomorphic to the Hilbert cube `Q = [0,1]^ℕ`. Then
for every `N` and `ε > 0` there is a c.p.c. order zero map `φ: M_N → A` with
`τ(1 − φ(1)) < ε` for every `τ ∈ T(A)`.

**Why the Hilbert cube.** It is the model strongly infinite-dimensional boundary.
- Every positive result on main needs a covering hypothesis on `K`: finite
  dimension, Lin's condition (C), countable dimension, or property C
  (`bauer-c-space-strict-comparison-divides-unit`). The Hilbert cube satisfies none.
- By `bauer-strict-comparison-pure-iff-divisible-unit`, the claim is equivalent to
  purity of every such `A`. For nuclear `A` with tracially locally finite nuclear
  dimension it is equivalent to `Z`-stability
  (`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`).

**Quantitative form** (`bauer-unit-division-metric-order-criterion`). Give `Q` the
metric `ρ(x,y) = Σ_i 2^{−i}|x_i − y_i|`, and let `ℓ_A(ω)` be the Lebesgue number of the
cover of `K` by division sets of weight `1/N + δ ≤ ω`. Since
`ord_Q(r) ≤ log_2(4/r) + 2`, the claim holds for `A` iff
`liminf_{ω→0} ω · log_2(1/ℓ_A(ω)) = 0`.
- *If.* This makes `ω · ord_Q(ℓ_A(ω))` tend to 0 along a sequence, and Corollary F
  applies.
- *Only if.* If the unit divides, `K` itself is a division set of every weight, so
  `ℓ_A(ω) ≥ 1`.

So a counterexample confines the local divisions of matrix size `N` to sets of
`ρ`-diameter `2^{−cN}`, heuristically pinning about `cN` coordinates.

**Base status.** Theorem E, Proposition 8.2 and Corollary F on main
(`research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md` and parts 1–3)
have no ex-verify review yet (`ex-verify2-analysis` unreviewed list). Lane
`ex2-tw-hilbert-cube-boundary` rechecked by hand Lemma 3, Steps 4–6 of Section 3,
Lemma 8.1 and the bounds of Proposition 8.2, and found no error.

## Attempts

- **Staircases and moves (Proposition 8.2).** Each active member pays about
  `1/N_i` of rank overshoot, from its one partly switched-on piece.
  - Suppose division sets of matrix size `N` do not meet both faces `x_j = 0` and
    `x_j = 1` for any `j ≤ D`. Lebesgue's covering theorem on the face `[0,1]^D` then
    forces a point in `D + 1` members, so the charge there is at least `(D + 1)/N`.
  - So the method fails exactly when `D` grows linearly in `N`. The same dimension
    count defeats every choice of per-member thresholds: a partition of unity
    subordinate to a cover of small mesh is an `ε`-map onto a `D`-dimensional nerve
    cell, and coordinatewise rounding of its values has error about `D/2` somewhere
    on that cell (heuristic count, not written as a proof).
- **Bootstrapping inside hereditary subalgebras.** Correct the rank error `c` of a
  first staircase inside `her(W)`, where pieces have size `c/N`.
  - Division sets of `her(W)` come from those of `A` at matrix size `NL`, which pin
    about `cNL` coordinates. So the corrected error is again about `c`.
  - The confinement rate is scale invariant, and iteration does not reduce it.
- **Rotating pieces instead of switching them.** Rotating a projection by central
  cosines keeps its rank, so a transfer between members costs no overshoot.
  - **Budget.** A transfer needs a free target slot, orthogonal to the pieces that
    are on. At a point with `D` simultaneous transfers the budget is `t + D/N < 1`.
  - **Cocycles.** For one slot, the map "which member holds it" is an `ε`-map into the
    nerve. On a `D`-dimensional face it cannot land in the 1-skeleton, so some point
    shares the slot among about `D + 1` members. That needs intertwiners among
    `D + 1` pieces that compose consistently on multiple overlaps.
  - **Where it dies.** Correcting inconsistent intertwiners needs central-parameter
    homotopies of unitaries in corners of the local tracial ultrapowers `A^ω_Y`, in
    every dimension up to `D`. Nothing on main supplies them without complemented
    partitions of unity or uniform Gamma. At a fixed precision each homotopy step
    also loses a square root of the defect.
- **Selection analogy (heuristic).** Local divisions form an lower semicontinuous
  family with contractible fibres. Selection theorems for such families hold on
  C-spaces and fail in general on the Hilbert cube (Uspenskij). No specific
  counterexample family was matched to an algebra.
