---
rg: 2
id: atlas-four-leg-frame-proves-one-cut-extraction
kind: route
title: Sum the four-leg comb blocks to obtain the Atlas asymmetric one-cut
target: atlas-one-cut-finite-multiplicity-extraction
requires:
  - atlas-four-leg-coordinate-frame-extraction
---

Let `E_1,...,E_4,W` satisfy `(FCF1)--(FCF2)` and put

```text
P=E_1+E_2+E_3.
```

Orthogonality of the four legs and `sum_i E_i=1` give the exact identities

```text
||(1-P) W P||_2^2
  = sum_(j=1)^3 ||E_4 W E_j||_2^2,                  (4LF1)

||P W (1-P)||_2^2
  = sum_(i=1)^3 ||E_i W E_4||_2^2
  >= ||E_1 W E_4||_2^2.                             (4LF2)
```

For `(4LF1)`, expand `E_4WP=sum_j E_4WE_j`; the summands are
Hilbert--Schmidt orthogonal because their initial projections are
orthogonal.  The proof of `(4LF2)` is the same with orthogonal range
projections.

Substitution of `(FCF1)--(FCF2)` yields

```text
||(1-P) W P||_2^2 <= C delta^c,
||P W (1-P)||_2^2 >= 1/64-C delta^c.
```

This is `atlas-one-cut-finite-multiplicity-extraction` with the explicit
constant `c0=1/64`.  No singular-value estimate or coordinate reconstruction
is used after `(FCF1)--(FCF2)`; all of that content is localized in the
four-leg frame claim.
