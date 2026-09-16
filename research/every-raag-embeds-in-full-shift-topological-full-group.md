---
rg: 2
id: every-raag-embeds-in-full-shift-topological-full-group
kind: claim
title: Every right-angled Artin group on a finite graph embeds in the topological full group of the two-sided binary full shift
distinct_from:
  shift-raag-family-is-always-lef-and-sofic: that is about approximation properties of a two-generator family of right-angled Artin groups; this embeds every finite-graph right-angled Artin group in the full group of the full shift.
---

For every finite simple graph `Γ`, the right-angled Artin group
`A_Γ = ⟨t_u (u ∈ V(Γ)) | [t_u, t_w] = 1 for {u,w} ∈ E(Γ)⟩` is isomorphic to a
subgroup of `[[{0,1}^Z]]`, the topological full group of the two-sided binary
full shift.

**Credit.** V. Salo, arXiv:2103.06663v1 (11 Mar 2021), Section 3, Theorem "For
every alphabet $\Sigma$, every RAAG embeds in $\llb \Sigma^\Z \rrb$", which also
covers countably infinite graphs. Salo derives it from a graph-product theorem
proved with conveyor belts. The route here specialises that construction to
finite graphs and vertex groups `Z`, and proves it completely. It was checked
exactly on six small graphs by
`experiments/raag-conveyor-belts-full-shift-2026-09-16/belts.py`.

Route: `raags-in-full-shift-full-group-conveyor-belt-proof`.
