---
rg: 2
id: nonhyperlinear-from-a4-t30-covariance-wall
kind: route
title: Opposite q14 and 19243-assisted t30 bounds rule out the regular atlas microstates
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-a4-context-exact-regular-normalization
  - atlas-word-19243-is-kernel-relation
  - atlas-q14-forces-t30-covariance-floor
  - atlas-a4-t30-energy-ceiling-below-q14-wall
---

Assume the binary Leavitt unit group is hyperlinear and take the normalized
exact-regular atlas necessity sequence.  Both `q_14` and `q_19243` lie in the
kernel of the two-chart Leavitt map, so after regularization

```text
||q_14(U_n)-1||_2 ->0,
||q_19243(U_n)-1||_2 ->0.                             (1)
```

The q14 covariance theorem applied to the first limit gives

```text
liminf_n x_30(U_n)^2 >=1/8.                           (2)
```

The exact-regular A4 normalization, the thirty packet relations, and the
second limit put the same sequence under the hypotheses of the one-coordinate
ceiling, which gives

```text
limsup_n x_30(U_n)^2 <1/8.                            (3)
```

Equations `(2)--(3)` contradict each other.  Hence the required hyperlinear
necessity sequence does not exist, and the explicit binary Leavitt unit group
is non-hyperlinear.

Relative to `nonhyperlinear-from-a4-root-energy-ellipse`, this route replaces
the full weighted S3 argument and the `3/128` four-root ellipse by one strict
covariance estimate for the single aligned transvection `t30`.
