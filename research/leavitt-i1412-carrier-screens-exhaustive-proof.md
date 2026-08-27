---
rg: 2
id: leavitt-i1412-carrier-screens-exhaustive-proof
kind: route
title: Enumerate the exact cofacial forests for both inverse carriers
target: leavitt-i1412-carrier-screens-exhaustive
requires:
  - minimum-block-noncrossing-enumeration-is-not-exhaustive
  - leavitt-d4-l14-i1412-corrected-eq3-retraction-skeleton
---

Use the cofacial forest criterion: in every interval forest, top-level block
colors are pairwise distinct; in each gap of a block, the child forest is
recursively maximal and no top-level child has the parent's color.  These
conditions are necessary and sufficient because two blocks are mergeable
exactly when they are cofacial.

The exhaustive forest generator is independently validated against brute
force on every three-color word of length at most eight.  Applying it to the
audited `COLORS` arrays returned on MSI:

```text
job 16679815 (Eq3): maximal=9894,  histogram={15: 9894}
job 16679829 (Eq1): maximal=70798, histogram={16: 70798}
```

The counts equal the earlier global-minimum screens and have no higher-block
leaves.  Hence the general minimum-block gap does not occur for either exact
carrier word.
