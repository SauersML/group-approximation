---
rg: 2
id: complement-boundary-upper-bound-proof
kind: route
title: Test the complement infimum with the identity and expand four blocks
target: complement-energy-is-bounded-by-polar-modulus-and-boundary
requires:
  - projective-transfer-reduces-to-complement-unitary-extension
  - canonical-fold-leak-is-complement-energy-or-h-singularity
---

Choose the identity complement, expand its commutator with the exact ambient
lattice representation, and bound the two boundary rows by compression
leakage.  Factor the retained block as `rho_c|T_c|` to separate polar
commutator error from modulus mismatch.  Combining the resulting upper bound
with the established canonical complement-energy lower bound gives `(CMB7)`.
