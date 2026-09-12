---
rg: 2
id: fpbs-quantitative-routing-tail-bound
kind: claim
title: Ambient expansion quantitatively forces long routes in near-unit-degree connected invariant subgraphs
root: true
invalidates:
  - fpbs-dead-uniform-tight-routes-contradiction
---

**Statement.** Let G be a nonamenable d-regular Cayley graph with unnormalized edge Cheeger constant
h. Let H be an invariant random connected spanning subgraph and put delta = E deg_H(o)/2 - 1. Then for
every integer R>=1,

    (1/d) sum_{s in S} P(d_H(o,s) > R) >= h/d - delta |B_G(o,R)|.

Consequently, for any sequence of such subgraphs with delta tending to zero, the liminf of the averaged
tail at each fixed R is at least h/d, and the mean route length has an explicit logarithmic lower bound
as delta tends to zero. This is a quantitative form of the obstruction that near-cost-one invariant
graphings cannot route the original generators over bounded distances. It is not a proof of either
universal goal and is not claimed to be new.

**Proof location.** `research/artifacts/fpbs/routing-obstruction-continuation.md`, Sections 2 and 3.
The argument thins the wired forest independently by eta so that its components are finite, deleting
intensity delta+eta from H. The ambient boundary of those finite components has expected root incidence
at least h by mass transport. A generator pair separated by this finite partition either has H-distance
greater than R or sees a deleted edge inside B_R, and the second event has probability at most
|B_R|(delta+eta). Let eta decrease to zero.

**Imported inputs.** Aldous-Lyons, *Processes on Unimodular Random Networks*, Theorem 6.2 and
Proposition 7.1, for the wired forest of expected degree two with at most two ends per component,
carried by `fpbs-wired-forest-degree-two`. The archive cites an author-hosted version and gives no
arXiv identifier, so this import could not be machine-checked. Mass transport on unimodular random
networks is used in the standard form.

**Finite-replay evidence.** `research/artifacts/fpbs/routing-bound-replay.json` via
`scripts/replay_routing_bound.py`: passed, over cycle4, cycle5, complete4 and K_{3,3}, totalling 15,792
nested configurations, 184,096 pointwise checks and 30,960 averaged checks. The replay covers the
finite witness and incidence inequalities only, not the infinite prerequisites.

**Evidence level.** Written deduction from one non-arXiv import, with a passing finite replay of the
counting inequality. Not refereed, not formally verified. This is the quantitative half of the
archive's main obstruction; the qualitative half is
`fpbs-cost-one-routes-cannot-be-uniformly-tight`, which it now implies directly.
