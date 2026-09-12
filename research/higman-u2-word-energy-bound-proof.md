---
rg: 2
id: higman-u2-word-energy-bound-proof
kind: route
title: Reduce U(2) phases to signs and verify the full quaternion polynomial partition
target: higman-u2-word-energy-bound
requires: []
artifacts:
  - research/artifacts/higman-u2-bound.md
  - research/artifacts/higman-u2-bernstein-certificate.json
  - experiments/higman_u2_certificate.py
---

The energy difference is affine in the real parts of the four scalar
phases, so its U(2) values are convex combinations of its SU(2) values.
Quaternion multiplication bounds the relator energy below by the scalar
functions h_j in the artifact. Nonnegative marked trace is immediate;
negative marked trace leaves eight sign boxes for polynomial (P).

The supplied complete subdivision has 56 terminal boxes. Reconstructing
all 14,336 terminal Bernstein coefficients over Q gives minimum 1/36.
The nonnegative partition of unity and the full binary cover prove (P)
nonnegative at every point, hence the claimed energy bound everywhere.

Weighted direct sums prove the common-block extension. Word telescoping
with length five gives the perturbation bound, and the universal energy
ceiling four on larger blocks gives the dimension-fraction inequality.
All details and the exact verifier are in the artifact; no bounded
sampling argument or unproved all-dimensions premise enters this route.
