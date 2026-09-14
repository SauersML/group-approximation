---
rg: 2
id: li-finite-k-graph-full-groups-are-f-infinity
kind: claim
title: "Xin Li: full groups of finite higher rank graphs with two loops of each colour at every vertex are of type F_infinity"
distinct_from:
  primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple: that drops the loop hypothesis for primitive aperiodic 2-graphs by rescaling, a skew product and a product with the full 2-shift; this is Li's theorem, which needs at least two loops of each colour at every vertex.
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**ESTABLISHED (import).** Let `C` be a finite higher rank graph (a `k`-graph) with
vertex set `C^0` and degree map `d`. Suppose that for every vertex `v` and every
`1 <= j <= k` there are at least two elements of `C` of degree `ε_j` with range and
source `v`. Let `X ⊆ Ω_∞` be a closed invariant subspace and
`Y = ⊔_v Y_v` with each `Y_v` empty or `X(v; v d^{-1}(e_P))` for some `e_P ⊆ S_P`.
Then the topological full group `F((I_l ⋉ X)_Y^Y)` is of type `F_∞`, in particular
finitely presented.

Li states his main results for the boundary groupoid `I_l ⋉ ∂Ω` (TeX l.593). Here
`Ω_∞ = Ω \ {χ_x : x ∈ C}` (TeX l.1126).

Source: X. Li, *Left regular representations of Garside categories II. Finiteness
properties of topological full groups*, Groups Geom. Dyn., arXiv:2110.04505. The
corollary is in the subsection "Higher rank graphs" (TeX l.2140) and follows from
Theorem `thm:k-graphs` (TeX l.2124–2127).

Route: `li-finite-k-graph-full-groups-f-infinity-citation`.
