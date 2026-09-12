---
rg: 2
id: second-order-step-beats-a-blocked-linearization
kind: claim
title: A neutral direction whose quadratic term cancels the blocked residual gives a three-halves step
distinct_from:
  quadratic-descent-loss-is-admissible-linear-is-not: that compares loss rates of a dimension-descent operation against a fixed threshold; this is a single correction step for a residual map whose linearization is not surjective, and produces the rate rather than assuming it.
  word-taylor-remainder-has-a-fourth-moment-bound: that bounds the remainder of one Taylor expansion of a word map in normalized Schatten norms; this is the correction step built on top of such an expansion, in arbitrary finite-dimensional normed spaces.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**ESTABLISHED.**  Let `F : E -> Y` be `C^3` on a ball of radius `r_0` about `x`
in finite-dimensional real normed spaces, `L = DF(x)`, let `Pi` be a projection
of `Y` onto a complement of `ran L`, and let `R` be a right inverse of `L` on
`ran L`.  Fix bounds `||R|| <= rho`, `||I - Pi|| <= q`, `sup ||D^2F|| <= M_2`,
`sup ||D^3F|| <= M_3` on that ball, and put `e = ||F(x)||`.

Suppose there is an admissible direction `xi` with

```text
L xi = 0,        ||xi|| <= C sqrt e,
|| Pi ( F(x) + (1/2) D^2F(x)[xi, xi] ) || <= C e^(3/2).                 (SO1)
```

Set

```text
eta = - R (I - Pi) ( F(x) + (1/2) D^2F(x)[xi, xi] ).                    (SO2)
```

Then `||eta|| = O(e)`, `||xi + eta|| = O(sqrt e)`, and

```text
|| F(x + xi + eta) || <= C' e^(3/2)                                     (SO3)
```

for all `e` below a threshold, with `C'` and the threshold depending only on
`C, rho, q, M_2, M_3, r_0`.

The direction does nothing at first order and everything at second order: it is
a possible mechanism when part of the residual lies outside `ran L`, so
that no linear correction at this point can reach it. Higher-order terms
or changing the base point are other possibilities. A linearization that is surjective with
a bounded right inverse does not need this and gets the classical quadratic rate
instead.

**Where the mathematics actually is.**  The lemma is elementary second-order
analysis; every difficulty is in supplying `(SO1)` uniformly, and in supplying it
again at the new point with the same constants, since only a hypothesis closed
under its own output can be iterated.  In particular this claim asserts nothing
about any group-approximation problem: see
`iwahori-second-order-repair-space-is-empty` for vanishing of the projected
quadratic effect at exact compatible points, and
`iwahori-admits-neutral-quadratic-directions` for the open
supply question.

**Where the derivative bounds are used.**  The proof evaluates `D^2F` only at
the pairs `(xi, xi)`, `(xi, eta)`, `(eta, eta)` and `D^3F` only at
`(v, v, v)` for `v = xi + eta` along the segment.  So it is enough to have
`M_2, M_3` on a cone containing those directions, which is how the estimate is
used in normalized Schatten norms, where no bound on the full second
differential exists (`normalized-hs-taylor-remainder-is-not-dimension-free`).
