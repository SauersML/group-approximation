---
rg: 2
id: closed-surface-groups-are-contracting-rsgs
kind: claim
title: Every closed hyperbolic surface group, and hence every cocompact Fuchsian group, is isomorphic to a contracting rational similarity group (the first one-ended case of BBMZ-hyperbolic Question 1.1)
distinct_from:
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is Question 1.1 for all non-elementary hyperbolic groups; this is its closed-surface (and cocompact Fuchsian) case, the first one-ended family.
  surface-group-atoms-are-wall-arrangement-cells: that attacks this case through the horofunction coding, where the irreducible core is the open step; the route here uses the Bowen–Series Markov coding instead, where irreducibility is automatic.
  closed-hyperbolic-surface-groups-embed-in-thompson-v: that asks for an embedding in V (Question 4.7); a contracting RSG structure with trivial nucleus would put the group in the edge-shift Thompson group V_{Γ,E}; this claim allows a nontrivial finite nucleus.
---

**OPEN.** Route: `closed-surface-groups-contracting-rsg-via-bowen-series`. Steps 1–3 are proved from the source read, and Steps 4–5 remain open. A positive answer settles Question 1.1 for closed surface groups.

**Scope.** By `contracting-rsgs-closed-under-finite-index-overgroups`, it is enough to treat one orientable closed surface
group of each genus `g ≥ 2`. That then covers every group containing a closed surface group with finite index: every
non-orientable closed hyperbolic surface group, and every cocompact Fuchsian group (by Selberg's lemma).

## Why this coding and not the horofunction boundary

- **Where the old route is stuck.** In BBMZ's horofunction coding, the RSG property and the finite nucleus hold for every
  hyperbolic group. The one missing hypothesis is a single recurrent component of the atom-type graph
  (`sft-irreducible-core-iff-unique-recurrent-component`). No mechanism for it is known in the one-ended case.
- **What the Bowen–Series coding gives instead.** It is a Markov coding of `S¹` by group elements. The RSG property is
  automatic there, and irreducibility comes from exactness of the Bowen–Series map. So the open steps move to rationality
  and the finite nucleus. There the trouble is concrete: whether the two one-sided codings of a partition point
  resynchronize within a bounded delay.

## Lesson for general BH

- **The irreducible core is a property of the coding, not of the group.** A Markov boundary map given piecewise by group
  elements (a "Bowen–Series structure") makes a hyperbolic group an RSG. Its irreducible core is then the mixing of the
  map.
- **So Question 1.1 becomes a contraction question.** It is the same "bounded level defect" lemma that makes Pisot Stein
  groups contracting (`pisot-stein-groups-are-contracting-rsgs-proof`, step 3). The left and right codings of each
  discontinuity point must merge after a bounded delay, which is the cycle property of Katok–Ugarcovici.
