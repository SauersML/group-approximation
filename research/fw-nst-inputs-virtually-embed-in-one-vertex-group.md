---
rg: 2
id: fw-nst-inputs-virtually-embed-in-one-vertex-group
kind: claim
title: An FW group with an infinite cyclic central subgroup, whose finite-index subgroups have only finite-index or virtually central normal subgroups, virtually embeds modulo a finite normal subgroup into a single vertex group of any eventually similar host
distinct_from:
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that embeds a finite-index subgroup of any FW subgroup into a finite PRODUCT of vertex groups; this adds a normal subgroup dichotomy and forces a finite-index subgroup, modulo a finite normal subgroup meeting the center trivially, into ONE vertex group with the center intact.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that concludes residual finiteness when the vertex groups are self-similar tree automorphism groups; this makes no assumption on the groupoid and records exactly what a vertex group must already contain.
artifacts:
  - research/artifacts/hl-bh-deligne-host-2026-09-13.md
---

**ESTABLISHED** through `fw-nst-one-vertex-group-proof` (elementary given the
virtual embedding theorem; not independently reviewed; no novelty claimed).

**Setting.** As in `fw-subgroups-of-eventually-similar-groups-virtually-embed`:
`X` is a finite union of path spaces of a finite directed graph in which every
vertex has out-degree at least two, `H` is an eventually self-similar groupoid
of cone homeomorphisms with vertex groups `H_s`, and `G <= Homeo(X)` is
eventually `H`-similar.

**Hypotheses on `K <= G`.**
1. `K` has property FW. Property (T) suffices, by step 3 of the proof route of
   that theorem.
2. `z in K` is central of infinite order; put `Z = <z>`.
3. **(D)** For every finite-index subgroup `L <= K` and every `N` normal in `L`,
   either `[L : N] < infinity` or `[N : N cap Z] < infinity`.

**Statement.** There are a finite-index subgroup `L <= K`, a finite normal
subgroup `F` of `L` with `F cap Z = 1`, a vertex `s`, and an injective
homomorphism `L / F -> H_s`. The image of `L cap Z` in `L / F` is central and
infinite cyclic.

**Scope.** This is a transfer statement, not an obstruction. It says that an
eventually similar host brings such an input no closer to a finitely presented
simple group than the vertex groups of its own groupoid already do.
