---
rg: 2
id: atlas-a4-packet-hs-regular-cores-proof
kind: route
title: Apply the robust A4 compiler to the finite atlas triangle packet
target: atlas-a4-packet-hs-regular-cores
requires:
  - atlas-shortest-a4-triangle-packet
  - a4-triangle-hs-regular-core
  - leavitt-regular-atlas-hyperlinearity-criterion
---

In the canonical atlas criterion both `A8` chart restrictions are exact regular
representations.  Hence for every selected pair-cube its order-three and
order-two letters have their exact finite orders and zero normalized traces.
The pair-cube itself belongs to the fixed atlas kernel packet, so its
normalized-HS defect tends to zero.  Regular-character separation also makes
the fixed nonidentity mixed word `BA` asymptotically traceless.

Apply `a4-triangle-hs-regular-core` to each of the thirty pair-cubes.  Each
produces an exact regular A4 core with codimension `o(d_n)`.  The number of
triangles is fixed, so the sum of the thirty exceptional codimensions is still
`o(d_n)`.  This proves the claim.
