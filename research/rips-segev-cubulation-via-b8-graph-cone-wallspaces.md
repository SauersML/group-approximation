---
rg: 2
id: rips-segev-cubulation-via-b8-graph-cone-wallspaces
kind: route
title: Realize a Rips--Segev group as a B(8) cubical presentation with one graph cone and cubulate through wall quasiconvexity
target: rips-segev-groups-are-cocompactly-cubulated
requires:
  - rips-segev-graph-cones-admit-b8-wallspaces
  - b8-hyperbolic-cubical-presentations-cocompactly-cubulated
  - rips-segev-groups-are-hyperbolic
---

**Proof, given the premises.** Let `G = G(Γ_Φ)` be an original Rips--Segev
group with `girth(Φ)` large, as in `rips-segev-graph-cones-admit-b8-wallspaces`.

1. Let `X` be the long wedge of two circles for `<a>` and `<b>`
   (Jankiewicz--Wise, Construction 4.3). Let `Y -> X` be the graph analogue of
   that construction for `Γ = Γ_Φ`, as described in
   `rips-segev-graph-cones-admit-b8-wallspaces`.
   - The mapping cone `X* = <X | Y>` has
     `π_1 X* = π_1 X / <<image of π_1 Y>>`.
   - The image of `π_1 Y` in `π_1 X = <a> * <b>` consists of the labels of the
     closed paths of `Γ` at one base vertex. Its normal closure is the normal
     closure of the labels of all cycles of `Γ`.
   - So `π_1 X* = G` (Steenbock, arXiv:1307.0981, definition of the relator set
     `R` in Section "Rips-Segev groups revisited").
2. By `rips-segev-graph-cones-admit-b8-wallspaces`, after subdivision `X*` is a
   compact `C'(1/20)`, `B(8)` cubical presentation with one graph cone.
3. `G` is hyperbolic by `rips-segev-groups-are-hyperbolic`.
4. By `b8-hyperbolic-cubical-presentations-cocompactly-cubulated`, `G` acts
   properly and cocompactly on a CAT(0) cube complex.
