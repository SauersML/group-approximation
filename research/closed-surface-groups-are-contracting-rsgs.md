---
rg: 2
id: closed-surface-groups-are-contracting-rsgs
kind: claim
title: Every closed hyperbolic surface group, and hence every cocompact Fuchsian group, is isomorphic to a contracting rational similarity group (the first one-ended case of BBMZ-hyperbolic Question 1.1)
distinct_from:
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is Question 1.1 for all non-elementary hyperbolic groups; this is its closed-surface (and cocompact Fuchsian) case, the first one-ended family.
  surface-group-atoms-are-wall-arrangement-cells: that attacks this case through the horofunction coding, where the irreducible core is the open step; the route here uses the Bowen–Series Markov coding instead, where irreducibility is automatic.
  closed-hyperbolic-surface-groups-embed-in-thompson-v: that asks for an embedding in V (Question 4.7); a contracting RSG structure with trivial nucleus would put the group in the edge-shift Thompson group V_{Γ,E}; this claim allows a nontrivial finite nucleus.
  horofunction-lemma-holds-for-free-and-surface-groups: that proves the horofunction local-to-global lemma for surface groups through a Helly argument on walls; this uses the same wall calculus for the Bowen–Series coding.
---

**ESTABLISHED** by `closed-surface-groups-contracting-rsg-via-bowen-series` (lane `bh-partials`, 2026-09-18; lane
proof). **Referee PASS** (bh-ref-q11, 2026-09-18), with four repairs recorded in the route's Referee section, none changing the result. Corollary 1's
input `contracting-rsgs-closed-under-finite-index-overgroups` also passed review (bh-ref-q11, 2026-09-19), so the
cocompact Fuchsian case is refereed in full.
- Steps 1–4 rest on sources read at source: Katok–Ugarcovici arXiv:1610.00167, and Bowen–Series 1979, Lemmas 2.3–2.4.
- **Priority.** None claimed. A web search on 2026-09-18 found no answer to Question 1.1 for surface groups after BBMZ
  arXiv:2309.06224.

## Statement

Let `Γ` be the fundamental group of a closed orientable surface of genus `g ≥ 2`. It acts faithfully on the circle
Cantorized at the endpoints of the walls of Adler–Flatto's right-angled `(8g−4)`-gon tiling. In the Bowen–Series coding
of that space, `Γ` is a contracting RSG:
- the coding is an SFT on `2(8g−4)` arc states, with a primitive graph;
- canonical similarities are group elements;
- every element is rational;
- the nucleus is finite.

**Corollaries.**
1. Every non-orientable closed hyperbolic surface group and every cocompact Fuchsian group is isomorphic to a
   contracting RSG. This uses `contracting-rsgs-closed-under-finite-index-overgroups` and Selberg's lemma.
2. BBMZ-hyperbolic Question 1.1 has a positive answer for all of these one-ended groups. What remains is the other
   one-ended hyperbolic groups, such as closed hyperbolic 3-manifold groups and Kazhdan hyperbolic groups, and
   hypothetical infinitely-ended groups that are not virtually torsion-free.

## Why this coding and not the horofunction boundary

- **The horofunction coding.** There, the RSG property and the finite nucleus hold for every hyperbolic group, and the
  one missing hypothesis is a single recurrent type component.
- **The Bowen–Series coding.** It is a Markov coding of `S¹` by group elements.
  - The RSG property is automatic.
  - Irreducibility comes from exactness.
  - The finite nucleus comes from a geometric fact: the level of a cut point is the time its itinerary ray enters the
    carrier of its wall. Fellow travelling then makes the level defect under `h` equal to the Busemann shift, up to a
    bounded error.

## Lesson for general BH

- **The irreducible core belongs to the coding, not to the group.** A Markov boundary map given piecewise by group
  elements, whose itineraries are geodesic rays and whose cut points are wall endpoints, makes a hyperbolic group a
  contracting RSG.
- **What contraction needs.** It is a "level = Busemann time" statement. Bounded level defect for Pisot Stein groups
  (`pisot-stein-groups-are-contracting-rsgs-proof`, step 3) is the arithmetic instance of the same mechanism.
- **Where the general question now stands.** It reduces to finding such Markov (Bowen–Series or Cannon-type) codings
  with wall-like cut sets. Kazhdan hyperbolic groups have no walls (FW), which is exactly where
  `horofunction-lemma-holds-for-free-and-surface-groups` also stops.
