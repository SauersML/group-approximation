---
rg: 2
id: finite-pauli-seed-reducing-quarter-carrier
kind: claim
title: Finite Pauli correction produces an actual reducing quarter carrier
distinct_from:
  canonical-trace-tests-robustify-pauli-quarter-holonomy: That extracts a trace-window holonomy floor from two Atlas carriers; this exactifies one D8 seed and averages the contextual tuple to obtain a genuinely reducing carrier.
  pauli-quarter-holonomy-is-balanced-derived-reset: That derives a new Pauli pair from Atlas reflection polynomials; this installs the original tensor Pauli seed and proves its dimension-independent correction interface.
---

Let a finite shared-variable contextual presentation have a
dimension-independent normalized-HS structural rounding theorem. Adjoin
involutions `B,C`, commuting with every contextual generator, with

```text
[B,C]=J,       J central.                              (PSQ1)
```

There is a fixed dimension-independent `O(sqrt(E))` correction which first
turns `(J,B,C)` into an exact `D_8` representation, then rounds the contextual
tuple inside its commutant. After correction,

```text
Q_-=(1-J)/2,       Q_empty=Q_-(1+B)/2                 (PSQ2)
```

are actual projections, `Q_empty` reduces the entire rounded contextual
tuple, and

```text
tr_d(Q_empty)=(1/2)tr_d(Q_-).                         (PSQ3)
```

The presentation has the exact tracial extension obtained by tensoring the
perfect contextual model with the two-dimensional Pauli representation. In
canonical microstates, `tr_d(J)->0`, hence

```text
tr_d(Q_-)->1/2,       tr_d(Q_empty)->1/4.              (PSQ4)
```

The order of correction is essential: no spectral gap for the arbitrary
contextual centralizer is assumed.
