---
rg: 2
id: glue-lemma-from-small-triangle-defect
kind: route
title: Bound the affine orientation defect on planes, then globalize to a bounded label list
target: affine-orientation-glue-lemma
requires: [affine-orientation-triangle-defect-is-small, triangle-defect-globalizes-to-a-bounded-label-list]
---

**Invalidated by a refuted premise (2026-09-07).** The averaging implication
is still valid, but `affine-orientation-triangle-defect-is-small` is false
by `noisy-affine-selector-defeats-bounded-hitting`. The description below
records the earlier proposed route; it is no longer a live proof plan.

The earlier two-step architecture of this region: an analytic
estimate that noise and boundedness force product-uniform star defect to be
small, and the established averaging step that turns this into a
dimension-free hitting set `Q`.

The first is a hypercube-analysis statement about `T_rho f` with `f`
bounded.  The second is now closed with the sharp constants `L=2` and
`gamma=1-eta`: choose a line with at least the average star degree and use
its two points as `Q`.  Therefore this route has only the analytic premise
left open.

The sampling measure is load-bearing.  The analytic premise must output
star certificates on a high-density subset of the product-uniform measure
on `B x B`; density only under a conditioning whose marginal is biased away
from uniform `B` does not imply the glue lemma's conclusion.
