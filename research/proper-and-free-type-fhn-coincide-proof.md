---
rg: 2
id: proper-and-free-type-fhn-coincide-proof
kind: route
title: "Proper to free replacement for FH_n through finite joins over cell neighbourhoods"
target: proper-and-free-type-fhn-coincide
requires: []
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part1.md
---

Complete proof in Theorem C of
`research/artifacts/zp-fpn-fhn-2026-09-13-part1.md`, §2.

Outline:
1. Choose a finite subcomplex `C` containing the smallest subcomplex `K(e_j)`
   of a representative of each orbit of cells.
2. For each cell `e`, set `S_e = { g : K(e) ⊆ gC }`. This set is nonempty,
   finite (stabilizers are finite), equivariant (`S_{ge} = gS_e`) and
   monotone (`K(e') ⊆ K(e)` implies `S_e ⊆ S_{e'}`).
3. Let `W = ⋃_e e × J(S_e)` inside `X × J_n(G)`, where `J_n(G)` is the
   `(n+1)`-fold join of the discrete set `G`. Then `W` is a free `G`-CW
   complex with finitely many orbits of cells.
4. The preimage in `W` of an open cell `e` is `e × J(S_e)`, and `J(S_e)` is
   `(n−1)`-connected. So the `E^1` pages of the skeletal filtrations agree
   for `q ≤ n−1`, and `H_j(W) ≅ H_j(X)` for `j ≤ n−1`.

Unreviewed.
