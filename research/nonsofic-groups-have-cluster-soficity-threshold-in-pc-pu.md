---
rg: 2
id: nonsofic-groups-have-cluster-soficity-threshold-in-pc-pu
kind: claim
title: Every nonsofic group has a percolation soficity threshold between p_c and p_u
distinct_from:
  fpbs-benjamini-schramm-universal: that is the universal strict inequality p_c < p_u; this places a soficity threshold for cluster relations of nonsofic groups inside the closed interval, which gives the strict inequality only when that threshold exceeds p_c.
  sofic-groups-in-paunescu-sofic-action-class: that is the refuted assertion that every action of a sofic group is sofic; this is about subrelations of the Bernoulli relation of a nonsofic group, which are sofic below p_c and nonsofic above p_u.
artifacts:
  - research/artifacts/percolation-soficity-threshold-2026-09-12.md
---

**Theorem.** Let `G` be finitely generated and `S` a finite symmetric generating set. Couple Bernoulli bond
percolation on `Cay(G,S)` at all parameters through `Omega = [0,1]^E`, with `omega_p(e) = 1{xi(e) <= p}`.
Let `R_p` be the cluster relation on `Omega`: `xi ~ g^-1 . xi` iff the vertex `g` lies in the open cluster
of `1`. It is a subrelation of the orbit relation `R_G` of the free Bernoulli shift `G ↷ Omega`. Put
`Sof(G,S) = { p : R_p is sofic }`.

1. `Sof(G,S)` is a down-set containing `[0, p_c)`. It also contains `p_c` when `Cay(G,S)` is nonamenable.
2. If `G` is not sofic, `Sof(G,S) ∩ (p_u, 1] = ∅`.

So every nonsofic `G` has a threshold `p_sof(G,S) = sup Sof(G,S)` with

    p_c <= p_sof(G,S) <= p_u.

Cluster relations are sofic below `p_sof` and nonsofic above it. The same statement with "hyperlinear"
replacing "sofic" holds for every non-hyperlinear group.

**Why.**
- Soficity passes to subrelations, and `R_p` increases with `p`.
- Relations with finite classes are sofic.
- For `p > p_u` (`uniqueness-phase-cluster-relations-inherit-nonsoficity`), `R_p` restricted to the
  infinite cluster equals `R_G` restricted to a set of positive measure, and so it is nonsofic.

**Consequence.** For nonsofic `G`, one sofic cluster relation at some `p > p_c` forces `p_c < p_u`
(`nonsofic-benjamini-schramm-from-sofic-supercritical-clusters`).

**Instance.** The binary Leavitt unit group, for every finite generating set. There the cost and
`L^2`-Betti routes to `p_c < p_u` give nothing (`leavitt-unit-groups-have-fixed-price-one`).

Proofs: Sections 1--3 of the artifact.
