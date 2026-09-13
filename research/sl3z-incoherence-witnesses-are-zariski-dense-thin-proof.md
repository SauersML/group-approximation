---
rg: 2
id: sl3z-incoherence-witnesses-are-zariski-dense-thin-proof
kind: route
title: Induct over the tree hierarchy with polycyclic edge groups, then read off density, thinness and normal subgroups
target: sl3z-incoherence-witnesses-are-zariski-dense-thin
requires:
  - non-zariski-dense-subgroups-of-sl3z-are-coherent
  - coherent-graphs-of-groups-with-noetherian-edge-groups
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md
---

1. **The hierarchy is coherent.** Induct on `k`.
   - The base case `H_0` is `non-zariski-dense-subgroups-of-sl3z-are-coherent`.
   - Virtually solvable subgroups of `SL_3(Z)` are polycyclic-by-finite by
     Mal'cev, hence Noetherian. So
     `coherent-graphs-of-groups-with-noetherian-edge-groups` carries coherence
     from `H_k` to `H_{k+1}`.
2. **Items (i) and (iv).** These are the contrapositive of coherence of
   `H_0` and of `H`.
3. **Item (ii).** `SL_3(Z)` is finitely presented, and finite-index subgroups
   of finitely presented groups are finitely presented (Reidemeister–Schreier).
4. **Item (iii).** Suppose `N` is an infinite normal virtually solvable
   subgroup of `K`. The identity component of its Zariski closure is solvable,
   connected and normalized by the Zariski closure of `K`, which is `SL_3` by
   (i). So that component is trivial and `N` is finite, a contradiction.

This is Section 4 of the artifact.
