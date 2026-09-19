---
rg: 2
id: nonhyperlinear-from-a4-holonomy-coherence-gap
kind: route
title: The exact-regular A4 holonomy gap contradicts the packet-forced S3 floor
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-word-19243-is-kernel-relation
  - atlas-a4-context-exact-regular-normalization
  - atlas-packet-forces-two-s3-covariance-energy
  - atlas-a4-holonomy-coherence-gap
---

Assume the prerequisites and suppose the binary Leavitt unit group were
hyperlinear.  Use the necessity direction of
`leavitt-regular-atlas-hyperlinearity-criterion`.  As in the corrected A4
packet provenance, choose the canonical regular-chart sequence pulled back from
the hypothetical hyperlinear models so every fixed kernel word used here has
defect `o(1)`.  In particular the thirty A4 pair-cubes and `q_19243` do.

Simultaneous virtually-free exactification followed by
`atlas-a4-context-exact-regular-normalization` gives, on the same dimensions,
an exact context-network representation `sigma_n` with exact regular A8 and A4
vertex types and all non-tree stable letters `o(1)` from identity.  Every fixed
chart generator changes by `o(1)`, hence finite-word telescoping preserves

```text
||sigma_n(q_19243)-1||_2 -> 0.
```

The same perturbation changes each of the two fixed S3 covariance defects by
`o(1)`.  Therefore `atlas-a4-holonomy-coherence-gap` gives for the original
regular-chart sequence as well

```text
limsup_n (a_n^2+b_n^2) < 1/32.                         (1)
```

Because the collision kernel relation itself tends to one, the strengthened
quotient-necessity form of `atlas-packet-forces-two-s3-covariance-energy`
gives on that same sequence

```text
liminf_n (a_n^2+b_n^2) >= 1/32.                        (2)
```

Equations `(1)` and `(2)` contradict each other.  Hence the binary Leavitt unit
group is not hyperlinear.

This route deliberately needs only the **necessity-sequence** A4 holonomy gap,
not the stronger uniform ceiling for every small-defect finite atlas model.
