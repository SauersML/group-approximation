---
rg: 2
id: s-unit-twisted-prufer-radicals-have-isolated-hosts-proof
kind: route
title: Realize each Prüfer module K_𝔭/O_𝔭 as the corner quotient O_K[1/m]^k / O_S^k of a Cornulier block group over Z[1/m], twisted by S-units and unipotents, and apply the isolated-host theorem
target: s-unit-twisted-prufer-radicals-have-isolated-hosts
requires:
  - twisted-prufer-corners-embed-in-isolated-cornulier-hosts
  - ascending-hnn-of-isolated-groups-embed-in-isolated-groups
---

The proof is in the body of `s-unit-twisted-prufer-radicals-have-isolated-hosts`. It builds the
lattice datum `(m, r, Δ, L)` using the Chinese remainder theorem, the class group and Dirichlet's
S-unit theorem. It then applies Theorem A of the host node and takes finite products.
