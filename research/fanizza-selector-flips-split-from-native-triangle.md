---
rg: 2
id: fanizza-selector-flips-split-from-native-triangle
kind: claim
title: Fanizza selector flips split off from the native triangle and retain the stationary D8 holonomy
artifacts:
  - research/artifacts/fanizza-selector-flip-split-cell-audit-2026-08-21.md
distinct_from:
  selector-free-spin-reset-leaves-contexts-independent: that shows old and fresh selector extensions remain independent over a common spin subgroup; this constructs the split covariant representation of the actual incidence-flip group on one native triangle.
  fanizza-reflection-recurrence-has-s4-stationary-overlap: that supplies the prescribed-word stationary reflection factor; this proves adjoining all selector-flip symmetries does not disturb or charge that factor.
  central-character-regular-flow-defeats-finite-d8-return: that gives stationary negative-character flow through finite graphs of packet groups; this treats the proposed selector covariance and native triangle ingredients explicitly.
---

Let `K` be the finite elementary abelian incidence-gauge group supplied by
`gauge-doubling-gives-selector-flip-symmetries`.  For every finite packet
representation `pi`, the covariant direct sum

```text
Pi=direct_sum_(g in K) pi composed theta_g
```

has permutation implementers for all selector flips.  Since every logical
word is fixed by `K`, those implementers commute with the whole logical
machine-word algebra.

Consequently there is an exact finite-dimensional tensor model satisfying:

1. the flat native Fanizza triangle and all selector-flip covariance
   relations;
2. the ordinary reflection recurrence in its exact `S_4` stationary-overlap
   representation; and
3. an independent D8 packet with `tr(H)=1/8`.

Thus the native triangle plus selector flips cannot by themselves imply a
trace-cyclic proper return.  A successful return cell must contain a
non-split mixed relation coupling a selector implementer to the nonlinear
guarded C18 machine-word multiplicity.
