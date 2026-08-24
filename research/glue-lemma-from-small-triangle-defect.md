---
rg: 2
id: glue-lemma-from-small-triangle-defect
kind: route
title: Bound the affine orientation defect on planes, then globalize to a bounded label list
target: affine-orientation-glue-lemma
requires: [affine-orientation-triangle-defect-is-small, triangle-defect-globalizes-to-a-bounded-label-list]
---

The two-step architecture the whole region is organized around: an analytic
estimate that noise and boundedness force the cocycle defect on random
`F_2^2` planes to be small, and a combinatorial step that turns a small
defect into the dimension-free hitting set `Q`.

They are separate premises because they fail for different reasons and
would be proved by different people.  The first is a hypercube-analysis
statement about `T_rho f` with `f` bounded; the second is a
local-consistency-implies-global-structure statement about `F_2^k` with no
analysis in it at all.  Folding them into one premise would hide which half
is stuck.

The escape clause ("unless `f` has a bounded number of large ambient
low-degree influences") is carried by both premises identically, so it
passes through the composition unchanged.
