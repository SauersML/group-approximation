---
rg: 2
id: atlas-a4-packet-hs-regular-cores-proof
kind: route
title: Apply the robust A4 compiler in the necessity direction of the atlas criterion
target: atlas-a4-packet-hs-regular-cores
requires:
  - atlas-shortest-a4-triangle-packet
  - a4-triangle-hs-regular-core
  - leavitt-regular-atlas-hyperlinearity-criterion
---

Assume `Q` is hyperlinear and use the **necessity** construction behind
`leavitt-regular-atlas-hyperlinearity-criterion`.  The pulled-back models of
`Q` kill the whole kernel `Rbar=ker(bar_rho)`.  Hilbert--Schmidt stability of
the virtually free product corrects the two finite chart factors to exact
regular `A8` representations while changing every fixed word by `o(1)`.
Therefore the corrected relative-unitary sequence may be chosen so that all
thirty fixed radius-five pair-cubes have defect `o(1)`.

Their individual order-three and order-two chart letters have exact finite
orders and zero normalized traces because both chart restrictions are exact
regular representations.  These are exactly the hypotheses of
`a4-triangle-hs-regular-core`.  Apply it to each of the thirty pair-cubes.
Each produces an exact regular A4 core with codimension `o(d_n)`.  Since the
number of contexts is fixed, the sum of all exceptional codimensions is still
`o(d_n)`.

This uses no mixed-word trace assumption.  It also does not assert that an
arbitrary sequence satisfying only one finite usable relator list kills every
kernel word; that stronger statement would ignore the possible central phase
`Rbar/Nbar`.
