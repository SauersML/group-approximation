---
rg: 2
id: free-compressor-localization-via-steinberg-decoder
kind: route
title: Decode the finite conditional corner ring from Steinberg microstates
target: shared-bcs-carrier-localizes-free-compressor-quotient
requires:
  - finite-inclusion-is-free-self-compressor-quotient
  - atlas-steinberg-context-absorption
  - marked-hs-separation-forces-spectral-density
  - hs-steinberg-bcs-corner-kernel-is-linear-sofic
---

Use the finite coefficient presentation `(BCL1)--(BCL2)`.  Context
absorption wordizes its two-sided ideal with finitely many rank-five
Steinberg relators.  The root-kernel decoder turns every normalized-HS
Steinberg microstate into a rank-metric coefficient model.  In that model,
`(r_j-1)P_f=0` and `(FQS1b)--(FQS1c)` make the parent action on the forbidden
carrier factor through `B_f`, while its compressed child factors through
`A_f`.  The packet Reynolds rank-jump supplies the required positive-density
child-only sector.  When `P_f=0`, the conditional ideal vanishes and the
perfect infinite BCS/HNN representation remains exact with its mark.

The decoder is stated directly for the finite corner ring, so no unproved
transfer from the different Toeplitz coefficient algebra is used.
