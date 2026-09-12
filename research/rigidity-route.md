---
rg: 2
id: rigidity-route
kind: route
title: Rigidity route via flexible HS-stability
target: non-hyperlinear-group
requires: [wreath-flexible-hs-stability]
artifacts:
  - notes/OBSTRUCTIONS.md
---

Claimed reduction (notes/OBSTRUCTIONS.md §5, "Rigidity"): if `G` is flexibly
HS-stable then the wreath candidate is not hyperlinear. Lift `ρ|_G` to
genuine `π_m`, pad the lamp, apply the Kazhdan pair to the *genuine* adjoint
representation to place it near `π_m(Γ)′`; then `commutant_no_growth`
(commutant-no-growth, the one formalized step) makes `π_m(G)` normalize `π_m(Γ)′`
exactly, and two distinct lamps collapse against trace separation.

Complementary: Dogon (arXiv:2211.10492) proves the same shape for central
extensions by a cohomological engine — amplification-proof but blind to
split extensions.
