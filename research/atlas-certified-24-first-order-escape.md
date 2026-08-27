---
rg: 2
id: atlas-certified-24-first-order-escape
kind: claim
title: The twenty-four certified alignment classes do not control the raw S3 covariances even at first order
distinct_from:
  atlas-boundary-tangent-covariance-coercivity: that is the positive coercivity statement for the full 234-word first-boundary packet and for the five-word tangent screen; this is the matching negative statement for the 24 certified representatives, and it is what makes the constant in that claim depend on which words are quoted.
  atlas-charts-overlap-trivially: that is about the intersection of the two chart images; this is about the derivative kernel of a fixed 24-word subset of the boundary packet.
artifacts:
  - research/artifacts/atlas-asc-tangent-exact-2026-08-19.md
  - experiments/asc-exact-certified24.json
  - experiments/atlas_asc_tangent_exact.py
---

ESTABLISHED by the same exact group-algebra computation as
`atlas-boundary-tangent-covariance-coercivity`.

Let `S_24` be the 24 certified representative classes
(`CERTIFIED_REPRESENTATIVE_INDICES` of `atlas_certified_a8_alignment`), the
subset the classical alignment scan is built on.  At the classical fold the
derivative form of `S_24` has kernel of dimension **2358**, and the raw `S_3`
covariance form restricted to that kernel has operator norm exactly **6** --
not `1e-17`.

So there is a skew-Hermitian `A` annihilating all 24 certified words to first
order while moving both raw `S_3` covariances.  Consequently:

* no argument that quotes only the certified-24 set can reach
  `atlas-two-s3-covariance-collapse`, even infinitesimally;
* the five-word tangent screen `0, 11, 30, 44, 55` is not a convenience but
  the actual carrier of the first-order rigidity -- it cuts the kernel from
  2358 down to 120 and closes the leak.

This is a no-go about a proof ingredient, not about the atlas: the full
first-boundary packet does control the covariances at first order.
