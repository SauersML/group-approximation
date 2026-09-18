---
rg: 2
id: bh-class-decidable-amalgams-from-free-products-and-hnn
kind: claim
title: Free-product closure plus decidable-edge HNN permanence give closure of the Boone--Higman class under decidable amalgams and finite graphs of groups
distinct_from:
  bh-embeddability-survives-decidable-edge-hnn: that is the HNN permanence premise itself; this derives amalgam and graph-of-groups permanence from it together with free-product closure.
  boone-higman-via-decidable-edge-towers: that derives the conjecture from HNN permanence plus the OPEN tower claim decidable-groups-embed-in-decidable-edge-towers; this needs no tower claim, so it is not subsumed while that claim is open.
  bh-embeddability-forces-decidable-edge-membership: that shows the decidable-edge hypothesis is necessary (for doubles); this shows, under the two premises, that it is also sufficient for amalgams.
artifacts:
  - research/artifacts/gq-bh-bh-permanence-closure-reductions.md
---

**ESTABLISHED** by `bh-class-decidable-amalgams-proof`
(lane proof, elementary; no priority claimed).

Assume
- **(FP)** `𝓑` is closed under free products of two groups (equivalently (JE) ∧ (FZ),
  `bh-class-free-products-iff-joint-embedding-and-free-z`); and
- **(HNN)** `bh-embeddability-survives-decidable-edge-hnn`.

Then:
1. **Amalgams.** Let `A, B ∈ 𝓑` be finitely generated, `C` finitely generated, and
   `i_A: C -> A`, `i_B: C -> B` injective and given on generators, with `i_A(C)`
   decidable in `A` and `i_B(C)` decidable in `B`. Then `A *_C B ∈ 𝓑`.
2. **Finite graphs of groups.** Let `𝔾` be a finite connected graph of finitely
   generated groups in `𝓑`, with finitely generated edge groups whose images are
   decidable in the adjacent vertex groups and edge maps given on generators. Then
   `π_1(𝔾) ∈ 𝓑`.

**Scope.** The decidability hypotheses cannot be dropped:
`bh-embeddability-forces-decidable-edge-membership` gives a hyperbolic `G ∈ 𝓑` and
a finitely generated `N` with the double `G *_N G ∉ 𝓑`. Both premises follow from
`boone-higman-conjecture`. Neither premise is known.
