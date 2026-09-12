---
rg: 2
id: non-linear-sofic-group
kind: claim
title: Exhibit a group that is not linear sofic over some field
root: true
distinct_from:
  non-hyperlinear-group: that denies normalized Hilbert--Schmidt approximation; this denies normalized-rank approximation over one field, and neither property is known to imply the other.
  linear-sofic-nonsofic-group: that asks for a linear sofic group outside the sofic class; this asks for a group outside the linear sofic class over some field.
---

OPEN.  Exhibit a countable group `G` and a field `F` such that `G` is not
`F`-linear sofic.

The field matters.  Arzhantseva--Paunescu prove that `C`-linear soficity
equals `Q`-linear soficity (Theorem 6.5) and passes to finite fields of
varying characteristic (Theorem 8.2, Observation 8.4).  Their Question 8.6
asks whether it passes to one fixed finite field.  A group that is not linear
sofic over `F_2` need not fail over `C`.  Over a fixed computable field,
[[linear-soficity-recognition-has-a-pi2-upper-bound]] ties this root to a
single two-generator test group.

A non-weakly-sofic group would close this root for every field at once, by
[[linear-sofic-implies-weakly-sofic-over-every-field]].

## Attempts

- **Kaplansky over characteristic two.** By
  [[linear-sofic-group-algebra-is-stably-finite]], a one-sided inverse pair
  in `F_2[G]` makes `G` non-linear-sofic over every field of characteristic
  two.  The Leavitt unit group is the candidate, through
  [[leavitt-unit-group-algebra-not-directly-finite]], which is open.
- **Kaplansky for the Kun--Thom wreath.** Dead: its group algebras are stably
  finite over every field ([[kun-thom-wreath-stably-finite]]), so the rank
  obstruction there must be genuinely metric.
- **Transcribing the nonsoficity proof: dead in every rank row (2026-09-12, lane
  `weakly-sofic-extension`).**
  - Both permutation-specific steps of Kun--Thom 4.1 fail in normalized rank
    over every field:
    - rounding from property (T) ([[kazhdan-rank-rounding-fails-over-every-field]]);
    - one-piece transport (`research/artifacts/rank-row-compression-audit-2026-09-12.md`,
      Section 3).
  - The criterion itself remains a win--win. Over `C` it is
    [[c-linear-sofic-groups-kill-rigid-compression-defects]], and if it holds it gives
    this root with `F = C` through [[non-linear-sofic-via-c-rank-row-defect]].
  - Non-weak-soficity cannot be reached this way at all: the Kun--Thom wreath is weakly
    sofic and carries a rigid defect ([[weakly-sofic-groups-can-carry-rigid-defects]]).
  - See `research/artifacts/weakly-sofic-extension-metric-scope-2026-09-12.md`.
