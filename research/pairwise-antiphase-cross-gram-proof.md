---
rg: 2
id: pairwise-antiphase-cross-gram-proof
kind: route
title: Unitary invariance compares each cross-Gram operator with its negative
target: pairwise-antiphase-covariance-controls-cross-gram
requires:
  - partial-isometry-gram-is-range-overlap
---

Fix `i<j`, abbreviate `R=R_ij`, and change both signs simultaneously if
necessary so that the two target equations in `(PAC1)` have ideal signs `+1`
and `-1`.  Since `R` is unitary,

```text
T_i^*T_j=(RT_i)^*(RT_j).
```

The ideal signed product is

```text
(+T_i)^*(-T_j)=-T_i^*T_j.
```

For contractions `A,B,C,D`, the Schatten ideal inequality gives

```text
||A^*B-C^*D||_2
 <= ||A-C||_2||B||_infinity+||C||_infinity||B-D||_2.
```

Apply it with `A=RT_i`, `B=RT_j`, `C=T_i`, and `D=-T_j`.  This proves
`(PAC2)`.  Squaring and using `(a+b)^2<=2(a^2+b^2)` gives

```text
||T_i^*T_j||_2^2
 <= (1/2)(||D_(i,ij)||_2^2+||D_(j,ij)||_2^2).
```

The ordered sum counts every unordered pair twice, which proves `(PAC3)`
with constant one.  Finally,
`partial-isometry-gram-is-range-overlap` identifies each squared cross-Gram
norm with `tau(Q_iQ_j)`, proving `(PAC4)`.
