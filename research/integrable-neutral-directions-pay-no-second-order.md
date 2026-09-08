---
rg: 2
id: integrable-neutral-directions-pay-no-second-order
kind: claim
title: A neutral direction tangent to a curve of exact solutions has zero projected second-order obstruction
distinct_from:
  atlas-phase-jacobian-has-invertible-gauge-kernel: that shows the scalar gauge tangent lies in the kernel of one specific nonlinear Jacobian and is invertible as a matrix, a first-order statement about the Atlas phase holonomies; this is a second-order statement, for any C^2 residual map, about every kernel direction that integrates.
  atlas-cross-jacobian-cannot-pay-the-gauge-mode: that rules out bilinear cross-Jacobian terms paying the gauge mode in the Atlas energy; this rules out the projected quadratic term of the residual itself, and applies to any exact solution of any smooth residual.
  second-order-step-beats-a-blocked-linearization: that is the positive step, conditional on a neutral direction with a nonzero projected quadratic term; this is the negative screen that says which neutral directions can never be that direction.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**ESTABLISHED.**  Let `F : E -> Y` be `C^2`, let `F(x) = 0`, let `L = DF(x)`
and let `Pi` be a projection onto a complement of `ran L`.  Suppose `xi` is
integrable at `x`: there is a `C^2` curve `t -> x(t)` with `x(0) = x`,
`x'(0) = xi` and `F(x(t)) = 0` for all small `t`.  Then

```text
Pi D^2F(x)[xi, xi] = 0.                                                 (IN1)
```

**Screen.**  If every direction in `ker L` is integrable at `x`, the projected
quadratic form vanishes identically on `ker L`, and the hypothesis `(SO1)` of
`second-order-step-beats-a-blocked-linearization` cannot be met at `x` by any
kernel direction: the second-order mechanism has an empty search space there.
Since `D^2F` is continuous, the same form is `o(1)` on kernel directions at
points near such an `x`, so the mechanism is weak in a neighbourhood as well,
and any use of it must be at points bounded away from the exact locus.  The
quantitative version of that last sentence needs a description of how `ker DF`
moves off the exact locus and is not asserted here.

`(IN1)` is the reason a gauge symmetry supplies no corrective curvature: gauge
directions integrate by construction.  It is also the cheap first test for any
proposed quadratic-repair mechanism -- exhibit a neutral direction that does
*not* integrate, or stop.
