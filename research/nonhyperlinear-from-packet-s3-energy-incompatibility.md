---
rg: 2
id: nonhyperlinear-from-packet-s3-energy-incompatibility
kind: route
title: Opposite packet-only S3 energy bounds make the regular atlas infeasible
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-packet-forces-two-s3-covariance-energy
  - atlas-two-s3-covariance-collapse
---

Let

```text
Q=L_(F_2)(1,2)^x.
```

If `Q` were hyperlinear, `leavitt-regular-atlas-hyperlinearity-criterion` would
supply external multiplicities and relative chart unitaries `U_n` with

```text
delta_n=max_(s in bar_S)||pi_n(s)-1||_2 -> 0.
```

For their two fixed raw `S_3` covariance coordinates `a_n,b_n`, the established
packet-only 19243 wall gives

```text
liminf (a_n^2+b_n^2) >= 1/128.
```

But `atlas-two-s3-covariance-collapse` gives, from the same hypothesis
`delta_n->0`,

```text
a_n^2+b_n^2 -> 0.
```

This is impossible.  Hence the regular-atlas feasibility condition fails and,
by the iff criterion, `Q` is not hyperlinear.

This endpoint no longer needs a separately compiled raw source word, a proof of
its nontriviality, or a separating refinement of the atlas models.  Collision
19243 already supplies the positive covariance side directly from the packet;
the sole open mathematics on this route is the opposite covariance collapse.
