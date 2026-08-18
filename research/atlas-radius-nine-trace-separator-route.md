---
rg: 2
id: atlas-radius-nine-trace-separator-route
kind: route
title: Refute atlas hyperlinearity from a separator on its first mixed trace window
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - atlas-kernel-window-length-nine
  - atlas-radius-nine-trace-separator
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

`atlas-steinberg-rank-five-translation` fixes the explicit finite presentation
`Gamma_St`; `atlas-kernel-window-length-nine` makes radius nine the first
structurally mixed atlas window rather than an arbitrary truncation.  The open
radius-nine separator supplies an all-matrix-size robust inequality supported
on that window whose canonical group-trace value is negative.

If `Gamma_St` were hyperlinear, its regular character would have matrix
microstates.  Along such microstates every fixed `T_St` relator penalty tends
to zero and the radius-nine trace moments tend to their canonical values.
Taking limits in the separator inequality gives `P(lambda_Gamma_St)>=0`,
contradicting the certified value `<=-c`.  Hence `Gamma_St` is an explicit
nonhyperlinear group.

This is intentionally narrower than the generic
`atlas-matricial-trace-separator` interface: solving an unrestricted separator
problem could merely repackage nonhyperlinearity by duality, whereas solving
the radius-nine problem proves that the first mixed atlas window already
contains a bounded-complexity matrix/factor separation.
