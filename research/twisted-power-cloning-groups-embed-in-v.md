---
rg: 2
id: twisted-power-cloning-groups-embed-in-v
kind: claim
title: "Twisted direct-power cloning groups with two endomorphisms of a finite group embed in V"
distinct_from:
  twisted-direct-power-cloning-finite-groups-are-cocf: that imports co-context-freeness for V_(G,θ), the case φ0 = id, φ1 = θ; this proves embedding in V (which is stronger for finitely generated groups) for every pair φ0, φ1 with ker φ0 ∩ ker φ1 = 1.
  cloning-system-groups-on-finite-groups-embed-in-v: that asks for an embedding for every cloning system on finite groups; this settles only the local direct-power family, where the cloning maps act on the cloned coordinate alone.
artifacts:
  - research/artifacts/twisted-power-cloning-cf-action-2026-09-16.md
---

Let `G` be a finite group and `φ0, φ1 ∈ End(G)` with `ker φ0 ∩ ker φ1 = {e}`.

1. `G_n = G^n`, padding inclusions, trivial representation maps, and cloning maps
   `(g_1,…,g_n) ↦ (g_1,…,g_{k-1}, φ0(g_k), φ1(g_k), g_{k+1},…,g_n)` form a cloning
   system on finite groups (Witzel–Zaremsky Def. 2.18). Its Thompson-like group
   `T(G_*)` embeds in Thompson's group `V`.
2. The V-type group `𝒱_(G,φ0,φ1)` also embeds in `V`. Its elements are classes of
   finite lists `{(a_i, b_i, h_i)}`, where `{a_i}` and `{b_i}` are complete prefix
   codes over `{0,1}` in bijection, `h_i ∈ G`, `(a,b,h) ~ (a0,b0,φ0 h),(a1,b1,φ1 h)`,
   and the product is `{(a_i,b_i,h_i)}{(b_i,c_i,k_i)} = {(a_i,c_i,h_i k_i)}`.

For `φ0 = id`, part 2 is `V_(G,θ)` with `θ = φ1` as described by
Bodart–D'Angeli–Perego–Rodaro (arXiv:2608.02111v1, §3.1), so this recovers their
Theorem 3.2. That covers every twisted direct power `V_(G,θ)` of
`twisted-direct-power-cloning-finite-groups-are-cocf`, the repo's earlier candidate
counterexamples to the embedding question. Part 1 includes the two-monomorphism
variation of the guide's Example 3.1 (arXiv:1606.08762). Both parts also cover pairs
where neither `φ` is injective.

Proof: `twisted-power-cloning-groups-embed-in-v-via-cf-action`.
