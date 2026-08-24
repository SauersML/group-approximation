---
rg: 2
id: agent-free-compressor-one-row-kernel-reflection
kind: claim
title: Reflect one mixed payload--kernel coefficient row into a Hilbert carrier
distinct_from:
  hs-steinberg-bcs-corner-kernel-is-linear-sofic: That reconstructs a rank-metric model of the whole finite conditional corner ring; this asks only for the finitely many normal-generator rows on one selected payload carrier.
  bcs-atom-detects-its-e5-central-root: That puts a BCS atom on a nontrivial root support; this additionally reflects multiplication by one free-kernel word on that support.
  agent-free-compressor-payload-kernel-fixed-sector: That states the representation-wide adjoint localization output; this specifies the mixed coefficient rows and asks for a stronger Hilbert-corner output from which the adjoint projection is automatic.
---

**OPEN ONE-ROW METRIC REFLECTION GATE.**  Let `theta:F->B` and
`r_1,...,r_s` be the fixed finite quotient and finite normal generating list
used by `agent-free-compressor-payload-kernel-fixed-sector`.  In the finite
rank-five Steinberg wordization, use one selected shared-BCS forbidden
idempotent `P` and impose the coefficient rows

```text
[P,x_i]=0,                      (x_i in a free basis X),
(r_j-1)P=0.                    (1<=j<=s)               (ORK1)
```

The target is the following dimension-uniform consequence for canonical
normalized-HS microstates.  After the standard finite-menu rounding, extract
a Hilbert-space projection `e` such that

```text
tr(e)>=c q_bad-o(1),                                    (ORK2)
||[e,U(x_i)]||_2=o(1),                                  (ORK3)
||(U(r_j)-1)e||_2=o(1).                                 (ORK4)
```

Only the fixed finite lists `X` and `{r_j}` occur.  No reconstruction of the
ambient coefficient ring, no rank-metric multiplicativity for arbitrary
coefficients, and no child quotient table are required.

This is the first payload relation not defeated by
`agent-free-compressor-kernel-multiplicity-firewall`.  In its tensor model,
the finite root table and quotient covariance remain exact, but `(ORK4)`
fails whenever the payload carrier is nonzero and the chosen kernel
representation moves it.  Conversely, in the exact perfect tracial BCS model
the forbidden idempotent is zero, so every row in `(ORK1)` is vacuous and the
marked free-HNN word remains available.

Thus `(ORK1)` has exactly the required logical polarity: it excludes the
stationary kernel-multiplicity types only on nonzero forbidden payload, while
placing no global quotient relation on `F`.  Proving `(ORK2)--(ORK4)` is a
strictly smaller metric-decoding problem than the current full Steinberg
corner-kernel theorem.

## Attempts

- Quotient covariance and finite root spectral support leave an arbitrary
  kernel representation on the multiplicity factor, by
  `agent-free-compressor-kernel-multiplicity-firewall`.
- The exact coefficient-module calculation proves `(ORK3)--(ORK4)`, but an
  abstract unitary microstate of the Steinberg wordization need not decode
  coefficient multiplication.  The unresolved step is precisely reflection
  of the fixed mixed products `(r_j-1)P`, not finite presentability.
