---
rg: 2
id: every-raag-embeds-in-brin-thompson-group-2v
kind: claim
title: Every finitely generated right-angled Artin group embeds in the Brin-Thompson group 2V
distinct_from:
  virtually-special-groups-embed-in-some-brin-thompson-group: that is the Belk-Bleak-Matucci embedding into nV with n = |V| + |E^c| growing with the graph; this fixes n = 2 for every finite graph.
  every-gl-n-z-embeds-in-2v: that asks for every GL_n(Z) in 2V, including groups with distortion elements such as H_3(Z); this is only the right-angled Artin groups, which sit in GL_N(Z) but do not exhaust it.
  z3-free-z-embeds-in-brin-thompson-group-2v: that is the single graph K_3 plus an isolated vertex, which refutes Belk-Bleak-Matucci Conjecture 1.7 at n = 2; this is every finite graph.
---

For every finite simple graph `Γ`, the right-angled Artin group `A_Γ` is
isomorphic to a subgroup of `2V`. Through `brin-thompson-nv-embeds-in-mv` it
embeds in `nV` for every `n ≥ 2`.

**Credit.** V. Salo, arXiv:2103.06663v1 (11 Mar 2021), abstract: "The group
$\llb X \rrb$ embeds in the higher-dimensional Thompson group $2$V, so it
follows that $2$V contains all RAAGs, refuting a conjecture of Belk, Bleak and
Matucci." The preprint is unrefereed; its only arXiv version is v1, and a
Crossref query on 2026-09-16 found no journal version.

**What it refutes.** Belk–Bleak–Matucci, arXiv:1602.08635v1, Conjecture 1.7: "A
right-angled Artin group A_Γ embeds into nV if and only if A_Γ does not contain
Z^(n+1) * Z." Take `Γ = K_{n+1} ⊔ K_1`. For `n = 2` this is
`z3-free-z-embeds-in-brin-thompson-group-2v`. The obstruction at `n = 1` still
holds (Bleak–Salazar-Díaz, as quoted in arXiv:1602.08635: `Z^2 * Z` does not
embed in `V`), so `V` and `2V` differ sharply on right-angled Artin groups.

**Limit.** This does not reach `H_3(Z)`, `BS(1,2)` or `SL_3(Z)`. Finitely
generated subgroups of topological full groups of full shifts have no distorted
elements (`subshift-crossed-product-gl-has-no-distorted-elements`; an elementary
proof is Part E of the artifact). So the route through `[[{0,1}^Z]]` cannot give
a yes to Zaremsky 2.19(c) or 2.19(d).

Route: `every-raag-in-2v-via-full-shift-full-group`.
