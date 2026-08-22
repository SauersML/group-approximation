---
rg: 2
id: constant-private-basins-reduce-same-basis-to-selected-code
kind: route
title: Feed a bounded-occurrence selected-label decoder through fixed private basins
target: same-basis-rounding-interface-for-sparse-weyl-sampler
requires:
  - constant-size-private-basins-give-uniform-root-control
  - bounded-occurrence-private-sampler-additive-decoder
---

Use one fixed basin for every selected X endpoint and every selected Z
endpoint.  Put the private mixed relation only at the two roots and put the
selected-label additive-code coordinate at each anchor.  Apply the assumed
decoder separately to the X and Z anchors.  Equation `(CPB1)` transfers its
average same-Hilbert rounding bound to the mixed roots with only the fixed
factor `C_H`.  The basins have linear total size and the mixed graph remains
a matching, so rooted dilution is removed without repeating a mixed pair.
Placement compatibility with contours through distinct basins is included
in the selected-code hypothesis.  This gives the same-basis conclusion
required by the target.
