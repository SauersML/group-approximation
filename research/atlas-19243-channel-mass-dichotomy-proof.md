---
rg: 2
id: atlas-19243-channel-mass-dichotomy-proof
kind: route
title: Diagonalize the two S3 reflection Laplacians
target: atlas-19243-forces-sign-or-standard-channel-mass
requires:
  - atlas-packet-forces-two-s3-covariance-energy
  - s3-standard-operator-channel-has-fivefold-reduced-gauge
  - atlas-19243-has-continuous-regular-s3-line-holonomy
---

Decompose Hilbert--Schmidt operator space with the three central character
projectors for diagonal `S3` conjugation.  The two-generator covariance form
vanishes on the trivial type.  Both transpositions act by `-1` on the sign
type, giving eigenvalue `8`.  In the standard type, the two reflection
matrices have sum with eigenvalues `1,-1`, so the covariance form has
eigenvalues `2,6`.  This proves `(CSM7)`.

Insert the packet and direct-relation energy floors from
`atlas-packet-forces-two-s3-covariance-energy`.  Pigeonholing the two terms
`8m_epsilon` and `6m_sigma` proves `(CSM3)--(CSM5)`.  The five-source count
gives the standard-source refinement.  Finally the exact continuous
line-holonomy family has no standard component, proving sharp necessity of
the sign alternative.
