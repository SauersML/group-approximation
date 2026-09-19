---
rg: 2
id: hyperlinear-nonsofic-from-group-table-conic-gap
kind: route
title: A finite conic gap, groupified coherently, separates hyperlinear from sofic
target: hyperlinear-nonsofic-group
requires:
  - finite-table-quantum-classical-hamming-gap
  - coherent-groupification-of-table-gap
---

The separation answer to Q3.4 in two halves, one finite and one global.

The first premise supplies a finite table `T` and `c > 0` with unitary models
of every accuracy but no permutation model of Hamming defect below `c` — the
local shape any hyperlinear nonsofic group must have, exposed as a dual
functional on the group-table conic face rather than as a rigidity property.
The second premise supplies a group `G`, hyperlinear, containing a nested
sequence of windows that asymptotically realize the quantum optimum while the
classical obstruction persists at every stage.  Then `G` is hyperlinear by
construction and not sofic: a sofic approximation of `G` would restrict to
permutation models of those windows with defect tending to zero, contradicting
the persistent gap.

What distinguishes this route from the other lanes into the same target is
where the obstruction comes from: not property (T), not a Clifford/crossed
product embedding, not a radical collision, but a finite conic certificate
that can in principle be found by search.  Its risk is concentrated in the
second premise — a gap that is realized by a genuine finite-dimensional
representation lands in a linear, hence sofic, group and proves nothing, so
the groupification must keep the certificate alive only in the approximate
regime.
