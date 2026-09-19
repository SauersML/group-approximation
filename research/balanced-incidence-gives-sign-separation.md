---
rg: 2
id: balanced-incidence-gives-sign-separation
kind: route
title: Apply the balanced Greendlinger theorem to the typed incidence presentation
target: colored-cayley-pauli-incidence-separation
requires:
  - balanced-pauli-incidence-labeling
  - balanced-greendlinger-separates-sign-cosets
  - sign-double-cosets-separate-pauli-clouds
---

Use the pure X and pure Z labeled cloud cycles as the equality relations and
the balanced mixed contours as the remaining graphical relators.  The
standard graphical-small-cancellation embedding gives actual Cayley
addresses and bounded edge offsets.  The balanced Greendlinger theorem gives

```text
<D_X>P_0<D_Z> intersect <D_X>P_1<D_Z> = empty.
```

These are exactly `(CCP1)`, so the relative-coset Pauli incidence compiler
applies: the nondegenerate Pauli sign table separates rows and columns, so
`sign-double-cosets-separate-pauli-clouds` supplies the two cloud-injectivity
clauses from the displayed double-coset separation.
