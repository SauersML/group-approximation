---
rg: 2
id: raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group
kind: claim
title: A right-angled Artin group inside Thompson's group V is a product of free groups, and no one-ended hyperbolic group virtually embeds in it
distinct_from:
  virtually-special-groups-embed-in-some-brin-thompson-group: that embeds virtually special groups in some nV through right-angled Artin groups; this shows the route yields only virtually free hyperbolic groups when n = 1.
  every-raag-embeds-in-brin-thompson-group-2v: that is Salo's embedding of all RAAGs in 2V; this is the sharp contrast for V, where only complete multipartite graphs occur.
  closed-mcg-finite-index-subgroups-do-not-embed-in-v: that uses the same Z^2 * Z obstruction for mapping class groups; this uses it to classify the RAAG subgroups of V and draws the hyperbolic consequence.
artifacts:
  - research/artifacts/gq-bh-bh-bbmz-problems-status.md
---

**ESTABLISHED** by `raag-subgroups-of-v-hyperbolic-proof` (lane proof, elementary,
not reviewed). It rests on the Bleak--Salazar-Díaz non-embedding of `Z^2 * Z` in `V`,
imported through the survey in `closed-mcg-v-nonembedding-via-koberda`. The
classification in part 1 agrees with the abstract of Corwin--Haymaker
arXiv:1603.08433: "We determine exactly which graph products, also known as Right
Angled Artin Groups, embed into Richard Thompson's group V. It was shown by Bleak and
Salazar-Diaz that Z² * Z was an obstruction. We show that this is the only
obstruction." No priority is claimed for part 1.

Let `Γ` be a finite simple graph with `A_Γ ≤ V`.
1. `Γ` is complete multipartite, so `A_Γ ≅ F_{n_1} × ... × F_{n_k}` is a finite
   product of free groups.
2. Every torsion-free non-elementary hyperbolic subgroup of a finite product of free
   groups is free.
3. So a hyperbolic group that virtually embeds in `A_Γ` is virtually free. In
   particular no one-ended hyperbolic group, and no closed hyperbolic surface or
   3-manifold group, virtually embeds in a RAAG lying in `V`.

The Belk--Bleak--Matucci and Salo embeddings of virtually special groups therefore
cannot reach `V` for any one-ended hyperbolic input
(`closed-hyperbolic-surface-groups-embed-in-thompson-v`).
