---
rg: 2
id: native-246-incidence-spectra-proof
kind: route
title: Diagonalize the digon, quadrangle, and hexagon incidence matrices
target: native-246-nonspherical-face-complex-has-explicit-gap
requires:
  - simple-kazhdan-kac-moody-lattices-exist
  - full-km-face-kills-no-spherical-gauge
---

For type `A_1 x A_1`, the generalized digon incidence graph is
`K_(q+1,q+1)`.  Its incidence matrix is the all-ones matrix, so after
division by `q+1` its singular values are `1` and `0`.

For type `B_2`, the generalized-quadrangle computation in
`native-b2-incidence-gap-and-spherical-absorber-proof` gives

```text
spec(N_13 N_13^*)={(q+1)^2,2q,0}.                     (NIS1)
```

This gives the middle line of `(NFC2)`.

For type `G_2`, the point-collinearity graph of the generalized hexagon of
order `(q,q)` is distance regular with intersection array

```text
{q(q+1),q^2,q^2; 1,1,q+1}.                            (NIS2)
```

On the distance partition around a point, its adjacency operator has the
tridiagonal intersection matrix

```text
[[0,       q(q+1), 0,       0],
 [1,       q-1,    q^2,     0],
 [0,       1,      q-1,     q^2],
 [0,       0,      q+1,     q^2-1]].                  (NIS3)
```

Its eigenvalues are

```text
q(q+1), 2q-1, -1, -(q+1).                             (NIS4)
```

If `N_23` is point-line incidence, then

```text
N_23 N_23^*=(q+1)I+A_col.                             (NIS5)
```

Substitution of `(NIS4)` yields eigenvalues

```text
(q+1)^2, 3q, q, 0,                                    (NIS6)
```

which proves the last line of `(NFC2)`.

For two orthogonal projections whose ranges meet in the spherical line, the
nontrivial eigenvalues of `(I-P)+(I-Q)` are `1 plus-or-minus s`, where `s`
runs through the nonconstant singular values of the cross-incidence map;
there are also eigenvalues `1` from unmatched directions.  This is the
two-projection principal-angle decomposition.  Applying it to `(NFC2)` gives
`(NFC4)`.  Direct sums and tensoring by a multiplicity Hilbert space preserve
the least positive eigenvalue, proving `(NFC5)--(NFC6)`.  The dimension
identity `(NFC7)` is the regular-restriction formula, so `(NFC8)` is
well-defined and is visibly the sum of the three squared shared-occurrence
differences.  Finally `C>=0` can only increase the quadratic form, so
`(NFC9)` follows once its only zero directions are the already quotiented
spherical gauges.
