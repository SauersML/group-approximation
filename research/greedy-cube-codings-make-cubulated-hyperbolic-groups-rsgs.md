---
rg: 2
id: greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs
kind: claim
title: If a hyperbolic group acts freely and cocompactly on a CAT(0) cube complex in which disjoint hyperplanes have disjoint limit sets, the greedy cube-path coding of the Roller boundary is a Markov SFT in which the group is an RSG with finite nucleus; it is a contracting RSG exactly when that SFT has a single recurrent component
distinct_from:
  right-angled-reflection-groups-in-h3-are-contracting-rsgs: that is the instance where the cube complex is the Davis complex of a right-angled reflection group, and conditions (a)–(c) prove the single recurrent component; this is the general cubulated statement, with that component left as a hypothesis.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this reduces it, for every cocompactly cubulated hyperbolic group (by Agol, every closed hyperbolic 3-manifold group), to two explicit conditions (NA) and (IRR).
  surface-group-atoms-are-wall-arrangement-cells: that gets an RSG with finite nucleus from the horofunction boundary and stops at irreducibility; this gets the same from the Roller boundary of a cubulation, and isolates irreducibility as the one combinatorial condition (IRR) on a finite graph.
---

**ESTABLISHED** as a conditional theorem by `greedy-cube-codings-rsg-proof` (lane `bh-partials`, 2026-09-18; lane proof,
not reviewed).

## Statement

Let a hyperbolic group `G` act freely and cocompactly on a locally finite CAT(0) cube complex `X`. Fix a
`G`-equivariant total order on the edges at each vertex; this is possible because the action is free. Consider:
- **(NA)** Distinct disjoint hyperplanes of `X` have disjoint limit sets in `∂G`. Equivalently, the stabilizers of two
  disjoint hyperplanes have finite intersection.
- **(IRR)** The greedy state graph `𝒢` below has a single recurrent strongly connected component.

**The coding.**
- The states are pairs `(r, S)`: a representative `r` of a vertex orbit, and a set `S` of edges at `r` that can be
  the set of edges whose hyperplanes separate `r` from some `ω` in the Roller boundary `∂X`.
- The greedy map moves from `r` across the smallest edge of `S`, then translates back to the representative of the new
  vertex.

**Then:**
1. The coding is Markov (**no hypothesis**).
2. Under (NA), the itinerary map is a `G`-equivariant homeomorphism `∂X ≅ Σ_𝒢`. `G` is an RSG there, and its nucleus is
   finite.
3. Under (NA) and (IRR), `G` is isomorphic to a contracting RSG.

**Instances.**
- The right-angled Coxeter tilings of `H²` and `H³` (`closed-surface-groups-are-contracting-rsgs`,
  `right-angled-reflection-groups-in-h3-are-contracting-rsgs`). There, walls are orthogonal or ultraparallel, which
  gives (NA). (IRR) holds by the Bowen–Series exactness, or by the face-graph conditions (a)–(c) with coset refinement.

## What this does to Question 1.1

- **The reduction.** Every closed hyperbolic 3-manifold group is cocompactly cubulated: Bergeron–Wise, with Kahn–Markovic
  surfaces, and virtually special by Agol (recalled, not re-read here). So for those groups Question 1.1 is reduced to
  finding one free cocompact cubulation satisfying (NA) and (IRR).
- **(NA).** It fails when two parallel hyperplanes have commensurable stabilizers, for instance two homotopic disjoint
  surfaces. The natural way to arrange it is a malnormal family of quasiconvex codimension-1 subgroups. Whether
  Bergeron–Wise families can be chosen malnormal is not settled here.
- **(IRR).** It is a finite check on `𝒢` for any given cubulation. In the Coxeter cases it followed from the
  non-adjacency pattern of one tile. The general analogue is a condition on vertex links: some edge avoids the link-star
  of every edge set `S`, and the resulting graph is connected and non-bipartite. That analogue is a conjecture here.
- **Kazhdan hyperbolic groups** have no cubulation (property FW), so this route cannot reach them.

## Lesson for general BH

- **What survives in general.** Three of the four ingredients of the Bowen–Series mechanism need only CAT(0) cube
  geometry:
  - the Markov property, from the Niblo–Reeves fact that separating hyperplanes at a vertex pairwise cross;
  - the RSG property, from a free action;
  - the finite nucleus, from "level = Busemann time" through carriers.
- **What does not.** The fourth, irreducibility, is combinatorial and not automatic.
- **Where the cubulated case of Question 1.1 now sits.** It is exactly (NA) plus (IRR).
