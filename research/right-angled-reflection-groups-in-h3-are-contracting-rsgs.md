---
rg: 2
id: right-angled-reflection-groups-in-h3-are-contracting-rsgs
kind: claim
title: The reflection group W of the right-angled hyperbolic dodecahedron, every finite-index subgroup of W (among them closed hyperbolic 3-manifold groups), and every group commensurable with W is isomorphic to a contracting RSG; the same holds for any compact right-angled polyhedron in H³ whose face non-adjacency graph is connected, non-bipartite, and misses the closed neighbourhood of every vertex
distinct_from:
  closed-surface-groups-are-contracting-rsgs: that settles Question 1.1 for closed surface groups through the one-dimensional Bowen–Series map; this is the two-dimensional (sphere-boundary) case, with a memoryless greedy map on the Roller boundary instead of a circle map.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this settles it for the commensurability class of the right-angled dodecahedral reflection group (and of each polyhedron satisfying the hypotheses), a class containing closed hyperbolic 3-manifold groups.
  surface-group-atoms-are-wall-arrangement-cells: that computes horofunction atoms from wall arrangements; here the states are cells of the arrangement of the face circles of one polyhedron, and the coding is dynamical.
---

**ESTABLISHED** by `right-angled-h3-reflection-rsg-via-greedy-roller-coding` (lane `bh-partials`, 2026-09-18; lane proof,
**not reviewed**).
- **The proof is self-contained.** It needs no Bowen–Series orbit equivalence and no ergodic theory:
  - the Roller boundary is the canonical Cantor model;
  - strong connectivity is a finite combinatorial check;
  - contraction reuses the "level = Busemann time" lemmas of `closed-surface-groups-contracting-rsg-via-bowen-series`.
- **Priority.** None claimed. A web search on 2026-09-18 found Bowen–Series-type maps for Kleinian groups only for
  continued-fraction and Bers-boundary settings, not this construction or Question 1.1.

## Statement

Let `F ⊂ H³` be a compact right-angled polyhedron with faces `1, …, m`, and let `W` be its reflection group. Let `𝒩` be
the graph on faces joining non-adjacent faces. Assume:
- **(a)** for every vertex `v` of `F`, some face is non-adjacent to all three faces at `v` and differs from them;
- **(b)** `𝒩` is connected;
- **(c)** `𝒩` contains an odd cycle.

Then:
1. `W` is isomorphic to a contracting RSG.
2. So is every finite-index subgroup `Γ ≤ W`, in particular every torsion-free one: the fundamental groups of the closed
   hyperbolic 3-manifolds that finitely cover the orbifold `H³/W`.
3. So is every group commensurable with `W`, by `contracting-rsgs-closed-under-finite-index-overgroups` applied to item 2.

**The right-angled dodecahedron** satisfies (a)–(c).
- Label the faces `m`; the ring `R_1` of its 5 neighbours; the ring `R_2` of 5 faces adjacent to the opposite face `o`;
  and `o` itself.
- **(a).** The three faces at a vertex, together with all their neighbours, are 9 faces. The 3 faces around the
  antipodal vertex remain.
- **(b).** `m`–`o`; `m`–each face of `R_2`; `o`–each face of `R_1`; and each face of `R_1` is non-adjacent to 3 faces
  of `R_2`.
- **(c).** `m` together with two non-adjacent faces of `R_2` is a triangle in `𝒩`.

So Question 1.1 holds for every closed hyperbolic 3-manifold group commensurable with the right-angled dodecahedral
reflection group. The Löbell polyhedra are expected to behave the same way; that has not been checked here.

## What this says about Question 1.1

- **Codings, not the group.** The Bowen–Series mechanism of the surface case is not special to dimension 2. Any
  cocompact reflection tiling with right angles gives a Markov coding by the memoryless rule "reflect in the
  smallest-labelled face plane separating you from the point". Its states are cells of the arrangement of the face
  circles of one tile.
- **Irreducibility is combinatorial.** It is conditions (a)–(c) on the face graph. Contraction is the carrier-entry
  lemma for walls.
- **What remains.**
  - One-ended hyperbolic groups not commensurable with such a reflection group: most closed hyperbolic 3-manifold
    groups (which are virtually special, but only as quasiconvex subgroups of right-angled Coxeter groups), and all
    Kazhdan hyperbolic groups (no walls).
  - For the 3-manifold groups, the natural next step is a quasiconvex-wall analogue of this coding, built from the
    Bergeron–Wise cubulation.

## Lesson for general BH

- **What a hyperbolic group needs to be a contracting RSG, in this approach.**
  - a **wall calculus** that computes the metric (right angles make face planes walls, and walls are ultraparallel or
    orthogonal);
  - a **greedy Markov rule** read off one tile, so that canonical similarities are group elements;
  - a **connected, non-bipartite non-adjacency pattern**, so that the coding is irreducible even after refining by the
    cosets of a finite-index subgroup.
- **Why cosets suffice for subgroups.** Finite-index subgroups are handled by refining states with cosets. That is why
  the whole commensurability class follows, not only `W`.
- **Two missing tools for other groups.** Kazhdan groups fail the first item. Generic 3-manifold groups fail the second,
  since their walls are only quasiconvex. So a "quasiconvex greedy coding" is the precise tool still missing for
  Question 1.1 on 3-manifold groups.
