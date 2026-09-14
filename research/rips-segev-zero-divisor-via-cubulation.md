---
rg: 2
id: rips-segev-zero-divisor-via-cubulation
kind: route
title: Cubulate the Rips--Segev groups, apply Agol, then Fisher--Sanchez-Peralta
target: rips-segev-groups-satisfy-kaplansky-zero-divisor
requires:
  - rips-segev-groups-are-cocompactly-cubulated
  - rips-segev-groups-are-hyperbolic
  - cubulated-hyperbolic-groups-are-virtually-special
  - fisher-sanchez-peralta-special-and-3-manifold-domains
---

**Proof, given the premises.** Let `G` be a Rips--Segev group, torsion-free
and hyperbolic by `rips-segev-groups-are-hyperbolic`, acting properly and
cocompactly on a CAT(0) cube complex `X`.

1. By `cubulated-hyperbolic-groups-are-virtually-special`, some finite-index
   `F <= G` has `X/F` special. The action of `F` is cocompact, so `X/F` is
   compact.
2. `F` is torsion-free and acts properly, so point stabilizers are finite,
   hence trivial. The action is free, so `F = pi_1(X/F)`.
3. So `G` is torsion-free and virtually the fundamental group of a compact
   special cube complex. By `fisher-sanchez-peralta-special-and-3-manifold-domains`,
   `k[G]` is a domain for every field `k`.
