---
rg: 2
id: sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups
kind: claim
title: Every finitely generated sofic group is a subgroup of an infinite finitely generated simple Kazhdan group that is F_2-linear sofic
distinct_from:
  amenable-groups-embed-in-simple-kazhdan-linear-sofic: that covers amenable inputs through a free minimal subshift over the overgroup and Følner rank models; this covers every sofic input through the lamplighter host, where no measured free minimal subshift is needed.
  sofic-groups-embed-in-simple-kazhdan-sofic-groups: that asks for a sofic (Hamming) envelope, which is open; this is the rank-metric envelope.
  lef-groups-embed-in-simple-kazhdan-lef-groups: that characterizes LEF groups with LEF envelopes; this extends the input class to sofic groups and weakens the envelope to linear soficity.
artifacts:
  - research/artifacts/sk-measured-subshift-lamplighter-rank-envelopes-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a finitely generated sofic group. Then `Γ` is a subgroup of an infinite,
finitely generated, simple group with property (T) that is `F_2`-linear sofic in the ultraproduct sense of
Arzhantseva–Păunescu. One may take `G = EL_3(LC(2^Δ, F_2) ⋊ (Z/2 ≀ Δ))`, with `Δ` the half-line overgroup of `Γ`.

**What it removes.** The rank route for non-amenable inputs previously needed a free minimal subshift over the
overgroup with an invariant measure and sofic labellings (`sofic-groups-have-measured-free-minimal-subshifts`, open).
The lamplighter action is only topologically free, but it carries the Bernoulli measure. Its models count over all
colourings of a sofic approximation (`sofic-lamplighter-bernoulli-crossed-products-have-rank-models`), so that input is
not needed.

**What it does not give.**
- Soficity of the envelope: the rank-to-Hamming barrier `gap-sofic-approximations-are-local-embeddings` is untouched.
- An equivalence: the converse only gives `F_2`-linear soficity of `Γ`.

**Credit.**
- Kionke–Schesler embed finitely generated residually finite groups in simple LEF groups, without (T).
- The half-line commutator is the Neumann–Neumann device, as credited on the overgroup node.
- Bounded novelty check: a grep of this graph, and Elek 2021, Bernshteyn 2019, Elek–Lippner and Kerr–Li read at
  source. No literature search for simple linear-sofic envelopes.

Route: `sofic-groups-simple-kazhdan-linear-sofic-envelope-proof`.
