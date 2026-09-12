---
rg: 2
id: clifford-total-energy-ledger-has-inverse-sqrt-log-critical-rate
kind: claim
title: A total-energy Clifford decoder has inverse-square-root-logarithmic same-model threshold
artifacts:
  - research/artifacts/section-three-quantitative-no-go-audit-2026-08-21.md
distinct_from:
  robust-clifford-capacity-bound: that starts with a complete-table approximate homomorphism and gives the exponential dimension bound; this computes the dimension-adaptive row threshold under a stated total-energy decoder.
  same-model-supercritical-clifford-trigger: that asks for a constant-sound compiler activating a supercritical Clifford system; this shows what a square-summation compiler would yield and why rowwise HS bookkeeping alone naturally loses `sqrt(log d)`.
  slofstra-subexponential-hyperlinear-profile: that derives a profile lower bound from a specific finite presentation with quantitative word-area loss; this is a normalization audit independent of that presentation.
---

**ESTABLISHED CONDITIONAL LEDGER.**  Fix `rho>0` and `A>=1`.  For matrix
dimension `d>=2`, put

```text
n(d)=2 floor(log_2 d)+4,       kappa=min(1/16,rho/42). (CTL1)
```

Suppose `n(d)` decoded challenge rows `R_j` produce, on an invariant corner
of dimension at most `d`, a complete-table `epsilon`-homomorphism of the
rank-`n(d)` Clifford group, with central-sign separation at least `rho`, and

```text
epsilon<=A (sum_j ||R_j||_2^2)^(1/2).                  (CTL2)
```

Here the row norms, `epsilon`, and `rho` are all normalized with the trace of
that invariant corner.  A separate positive-density estimate is required if
one wants to compare them with ambient normalized-HS energy.

Then every such model has at least one row satisfying

```text
||R_j||_2 >= kappa/(A sqrt(n(d))).                     (CTL3)
```

Hence the critical rowwise scale is `Theta(1/sqrt(log d))`.

This order is sharp for the inference from maximum row norm to total squared
energy.  For every `n`, take `n` equal orthogonal blocks with projections
`p_j` and involutions `z_j=1-2p_j`.  Then

```text
||z_j-1||_2=2/sqrt(n),
sum_j ||z_j-1||_2^2=4.                                 (CTL4)
```

Every block is a point-mass witness for one maximal local failure even though each
global row is only `2/sqrt(n)`.  Therefore no rowwise argument can improve
the order in `(CTL3)` without coupling the blocks or imposing a separate
anti-localization hypothesis.

There is a stronger, non-block-diagonal sharpness test.
`dirac-average-is-a-sharp-near-extra-clifford-generator` starts with `2m`
exact anticommuting generators on the irreducible `d=2^m` module and forms
their normalized sum.  The sum is itself an involution, has
anticommutator `sqrt(2/m)1` with every old generator, and exactly
anticommutes with chirality.  Thus the same `Theta(1/sqrt(log d))` boundary
already occurs coherently inside one Clifford factor; it is not merely an
artifact of orthogonal row localization.

Clause `(CTL2)` is not currently proved for growing local Clifford
presentations.  The existing local-relator-to-complete-table conversion has
additional polynomial normal-form loss.  Thus this theorem validates the
reported rate under its exact normalization; it does not claim an
unconditional new Clifford stability result.
