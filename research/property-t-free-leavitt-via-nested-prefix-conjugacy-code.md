---
rg: 2
id: property-t-free-leavitt-via-nested-prefix-conjugacy-code
kind: route
title: Collapse the marked root through the nested-prefix conjugacy-difference clique
target: property-t-free-leavitt-full-mf-radical
requires:
  - leavitt-nested-prefix-conjugacy-clique
  - leavitt-nested-prefix-conjugacy-uniform-area
  - bounded-area-conjugacy-difference-code-kills-mf-mark
  - full-leavitt-idempotent-defect-saturation
---

Use the complete graph on the nested prefix roots `b_m`.  The first two
requirements make every edge difference a uniformly bounded-area conjugate
of `z`.  The operator-norm coloring criterion therefore puts

```text
z in Rad_MF(Delta).
```

The MF radical is normal, and the saturation theorem says `z` normally
generates `Delta`.  Hence the MF radical is all of `Delta`.
