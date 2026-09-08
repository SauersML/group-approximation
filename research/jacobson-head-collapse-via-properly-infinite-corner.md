---
rg: 2
id: jacobson-head-collapse-via-properly-infinite-corner
kind: route
title: Dead. Try to collapse the Jacobson head by exhibiting a properly infinite corner
target: binary-jacobson-steinberg-head-root-is-mf-invisible
requires: []
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**DEAD.**  Recorded so that the obstruction has something to kill;
invalidated by `binary-jacobson-matrix-rings-have-no-infinite-corner`.

## The attempt

`properly-infinite-corner-forces-non-mf-from-rank-two` needs no fullness,
only a nonzero properly infinite idempotent somewhere in the ring.  The
binary Jacobson algebra `J = F_2<S,T | TS = 1>` has a nonzero defect
`Q = 1 - ST` and a corner `QJQ = F_2`, so it is natural to look for a
properly infinite idempotent either in `J` itself or, after stabilizing,
in some `M_d(J)`; the certificate would then kill `e_12(Q)` in every
norm-corona model and settle the head.

Matrix amplification is the plausible part of the attempt: `EL_n(M_d(J))`
sits inside `EL_(nd)(J)`, so a certificate at any finite `d` would be
enough, and no exhaustion of the unit is required by the certificate.

## Why it dies

`binary-jacobson-matrix-rings-have-no-infinite-corner` proves the search
space is empty: for every finite `d`, `M_d(J)` has no nonzero properly
infinite idempotent at all.  The symbol map kills any candidate `p`, and
the corner that survives is finite dimensional over `F_2`, where a split
injection of a space into two copies of itself is impossible.  So the
attempt fails for a dimension reason, not for want of a cleverer
certificate, and finite amplification does not repair it.

The target is established anyway, by
`jacobson-head-collapses-by-rank-weighted-transport`.  What dies here is
this particular fullness-free route to it, which would have avoided that
route's Kazhdan input.  It also cannot serve
`property-t-free-jacobson-head-collapse`, and for a second reason: the
certificate consumes `full-defect-ring-non-mf-at-rank-two`, whose own
proof uses property (T).
