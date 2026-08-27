---
rg: 2
id: mf-limits-are-created-and-colimits-are-reflected
kind: claim
title: Countable MF limits are created in groups and countable MF colimits are reflected
artifacts:
  - research/mf-limits-are-created-and-colimits-are-reflected-proof.md
---

For every diagram of countable MF groups whose ordinary group limit `L` is
countable, `L` is MF and is also the limit in the category of countable MF
groups.  Thus the inclusion of countable MF groups creates every limit which
remains countable, including finite products, equalizers, pullbacks, and
countable inverse limits with countable underlying group.

For every diagram whose ordinary group colimit `C` is countable, the colimit
in countable MF groups is `R_MF(C)`.  Hence the category has the exact
calculus

```text
limits:    compute in groups,
colimits:  compute in groups, then divide by Rad_MF.   (LC1)
```

In particular a countable inverse limit of MF groups is MF whenever its
underlying group is countable, while a pushout or quotient of MF groups may
acquire precisely the new radical removed by the final reflection.
