---
rg: 2
id: nonhyperlinear-via-canonical-btb-finite-tree
kind: route
title: Grow the binary-tetrahedral detected canonical carrier past its central two-sign capacity
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - maximal-forbidden-atom-has-a-named-positive-half
  - canonical-bcs-root-detection-via-binary-tetrahedral-bridge
  - protected-adaptive-btb-wordization-preserves-canonical-budget
  - canonical-btb-finite-depth-escape-tree
---

First use the **seed-protected** BTB extension supplied by
`protected-adaptive-btb-wordization-preserves-canonical-budget`: every
packet centralizes the marked sign and Pauli seed sign included in its edge
two-group, while conditional arrows remain free to switch Pauli sectors.
The unprotected extension
cannot be used here, because
`binary-tetrahedral-packet-hull-saturates-unprotected-seed-sign` makes its
initial common hull fill the entire capacity.

Assume the repaired extended group were hyperlinear and take canonical
microstates.  The initial common reducing hull then has trace tending to
`1/8`, while every reached carrier lies below the common negative sector of
`J` and `ell`, whose trace tends to `1/4`.  At each reached node the maximal
forbidden atom has mass at least

```text
(beta/M)tau(Q_sigma)-O(sqrt(E_pres)).
```

Equations `(CBR2)--(CBR3)` and reducing-hull carry-forward give a fixed
supercritical factor `1+eta beta/M`.  Choose `N` by `(CBR4)` and iterate the
finite error estimate.  The terminal carrier has trace strictly greater
than `1/4`, contradicting its containment in the common negative sector.

Bass--Serre normal form makes the auxiliary central involution nontrivial in
the abstract group.  The perfect tracial BCS representation extends with
`J=-1`, `ell=1`, and all auxiliary packets trivial, so in particular the old
marked word remains nontrivial.  The contradiction therefore excludes the
canonical microstates whose existence is equivalent to hyperlinearity.
