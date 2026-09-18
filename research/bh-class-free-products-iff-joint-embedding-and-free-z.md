---
rg: 2
id: bh-class-free-products-iff-joint-embedding-and-free-z
kind: claim
title: The Boone--Higman class is closed under free products iff finitely presented simple groups have joint embedding and each U * Z embeds
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Corollary F, free-product closure of the permutational class B_A; this concerns the full Boone--Higman class, where free-product closure is open.
  fp-simple-groups-have-the-joint-embedding-property: that is the joint embedding statement (JE) itself; this shows free-product closure is exactly (JE) plus (FZ).
artifacts:
  - research/artifacts/gq-bh-bh-permanence-closure-reductions.md
---

**ESTABLISHED** by `bh-class-free-products-iff-joint-embedding-proof`
(lane proof, elementary; no priority claimed).

With `𝓑` as in `bh-class-finite-extensions-reduce-to-finite-simple-wreaths`,
the following are equivalent.
1. **(FP)** `𝓑` is closed under free products of two groups.
2. **(JE)** ∧ **(FZ)**, where (JE) is `fp-simple-groups-have-the-joint-embedding-property`
   and (FZ) says `U * Z ∈ 𝓑` for every finitely presented simple `U`.

**Consequences.**
- (FZ) is the trivial-edge case of `bh-embeddability-survives-decidable-edge-hnn`,
  since `U * Z` is the HNN extension of `U` over the trivial subgroup. So (JE) plus
  decidable-edge HNN permanence implies (FP).
- (JE) follows from closure under finite direct products. Also `A * B <= (A x B) * Z`
  (see the proof). So closure under finite direct products plus (FZ) implies (FP).

**Calibration.** On the permutational class both (JE) and (FZ) hold, by BFFHZ
Corollary F. So (FP) can fail only through a finitely presented simple group
outside `B_A`.
