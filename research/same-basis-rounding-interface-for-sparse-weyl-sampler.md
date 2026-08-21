---
rg: 2
id: same-basis-rounding-interface-for-sparse-weyl-sampler
kind: claim
title: Round same-basis occurrence tests to one PVM without dimension loss
distinct_from:
  bounded-degree-entangled-agreement-pauli-metapixel: that is the complete mixed X/Z metapixel; this isolates its same-basis input.
---

OPEN.  Construct a bounded-degree, bounded-template, perfect-completeness
same-basis occurrence test with the following same-Hilbert conclusion.
From value at least `1-epsilon`, round all X occurrences (and separately all
Z occurrences) to one exact additive `F_2^n` action on a common marked
carrier, equivalently to one spectral PVM, with total squared normalized-HS
change at most

```text
C epsilon^theta
```

for constants independent of `n`, answer count, and ambient dimension.
The rounding may discard at most `C epsilon^theta` marked mass but may not
use a context-dependent family of PVMs, an equality fiber, or a flexible
dimension enlargement.

This is the exact input needed before
`sampled-weyl-defect-controls-common-pvm-dirichlet-energy`.  Ordinary dense
BLR supplies the algebraic conclusion but its complete pair table is not a
finite-template small-cancellation incidence object.  Equality-cloud degree
reduction recreates the known two-pair contour obstruction.

## Attempts

- **Dense BLR.**  Robust but its complete additive-triple incidence is not
  directly compatible with the bounded-template placement gate.
- **Expander equality clouds.**  They synchronize copies through repeated
  equality fibers and recreate short balanced contours.
- **Separate local roundings.**  These do not produce the common PVM needed
  for `(SW2)` and leave a coupling escape.

