---
rg: 2
id: partial-isometry-leakage-is-range-defect-proof
kind: route
title: Cycle the leakage square to the final projection
target: partial-isometry-leakage-is-range-defect
requires: []
---

Since `1-P` is a projection,

```text
||(1-P)T||_2^2
 = tau(T^*(1-P)T)
 = tau((1-P)T T^*)
 = tau((1-P)F),
```

where the middle equality is traciality.  Nothing about the initial projection
or the polar phase of `T` enters.