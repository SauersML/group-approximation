---
rg: 2
id: bs12-regular-padding-is-removable
kind: claim
title: Padding a BS(1,2) near-representation by the clock representation can be removed in operator norm in the same dimension
distinct_from:
  bs12-identity-padding-is-removable-in-operator-norm: that removes trivial-representation padding 1_k from an exact correction; this removes padding by the regular-trace clock representation, whose image is infinite-dimensional in the limit and so is not a fixed-point summand.
---

**OPEN.**

**Statement (RPR).**  For every `eps > 0` there are `delta > 0` and `N_0`
such that the following holds for all `n >= N_0`.
- `(A, B)` in `U(n)` satisfies `||A B A* - B^2|| <= delta`.
- `sigma` is the exact clock representation `(W_m, D_m)` of odd dimension
  `m` in `{n, n+1}`.
- `(A + W_m, B + D_m)` is within `delta` of an exact pair in `U(n+m)`.

Then `(A, B)` is within `eps` of an exact pair in `U(n)`.

**Status.**  RPR is necessary for TPC.  If TPC (equivalently ESS Q3, by
`bs12-identity-padding-is-removable-in-operator-norm`) holds, then
`(A, B)` itself is close to exact.  Together with Q3_full
(`bs12-faithful-trace-opnorm-correction`), RPR is also sufficient for TPC.
That is the route `bs12-trivially-padded-opnorm-correction-via-faithful-padding`.

**Why it is not the wave-12 argument.**  Wave 12 removed identity padding
using the fixed-point subspace of `t`.  An exact pair in `U(n+m)` near
`sigma`'s block has no invariant subspace near `C^m` a priori.  One needs
`C^n` to be almost invariant for the exact correction and an exact
restriction.  That is a relative (subrepresentation) form of norm
stability.  A candidate tool is the excision of fixed finite-dimensional
summands from representations of positive-rank traces (see
`bs12-full-lift-uniqueness-in-matrix-ultraproducts`, step (b)), applied to
the correction of `phi + sigma` rather than to `phi`.

## Attempts

- 2026-09-19 (swarm-0917-w15-w15-ptm-follow): stated as the second half of
  the decomposition of TPC.  No proof.
