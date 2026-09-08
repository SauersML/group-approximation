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
quadratic form vanishes identically on `ker L`: these directions cannot
change the projected residual to second order at this base point. At an
exact point `F(x)=0`, `(SO1)` is nevertheless satisfied trivially by
`xi=0`; there is no nonzero residual to cancel.

This is an assertion at the exact point. A useful nearby estimate needs
control of the moving kernel, the cokernel projection, and the derivatives
in the relevant norms. Continuity alone supplies no dimension-independent
near-sector exclusion and does not force useful correction directions to
remain a fixed distance from the exact locus.

`(IN1)` is the reason a gauge symmetry supplies no corrective curvature: gauge
directions integrate by construction.  It is also the cheap first test for any
proposed quadratic-repair mechanism: an integrable direction at an exact
point cannot supply a nonzero projected quadratic effect there.
