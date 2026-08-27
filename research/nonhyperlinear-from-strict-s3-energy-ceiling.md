---
rg: 2
id: nonhyperlinear-from-strict-s3-energy-ceiling
kind: route
title: Any S3 covariance ceiling below 1/128 contradicts the 19243 packet floor
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-packet-forces-two-s3-covariance-energy
  - atlas-two-s3-energy-ceiling-below-19243-floor
---

Assume the three prerequisites and suppose

```text
Q=L_(F_2)(1,2)^x
```

were hyperlinear.  The canonical atlas criterion gives relative chart
unitaries `U_n` with `delta(U_n)->0`.  The open ceiling claim therefore gives,
for all sufficiently large `n`,

```text
a_n^2+b_n^2 <= eta < 1/128.
```

But `atlas-packet-forces-two-s3-covariance-energy` gives on the same sequence

```text
liminf (a_n^2+b_n^2) >= 1/128.
```

Contradiction.  Hence `Q` is not hyperlinear.

This route records the actual quantitative budget left by collision 19243:
the atlas argument does not need exact covariance, approximate covariance, or
even an `o(1)` bound.  It only needs to save a fixed amount of S3 energy below
`1/128`.
