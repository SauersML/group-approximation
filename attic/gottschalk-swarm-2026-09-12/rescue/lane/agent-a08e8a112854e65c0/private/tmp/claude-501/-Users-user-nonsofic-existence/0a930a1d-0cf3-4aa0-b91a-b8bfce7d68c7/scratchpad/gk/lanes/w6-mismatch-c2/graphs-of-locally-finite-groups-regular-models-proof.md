---
rg: 2
id: graphs-of-locally-finite-groups-regular-models-proof
kind: route
title: Free actions transported along a maximal forest, permutation intertwiners on the other edges, and the D_8 rank count
target: graphs-of-locally-finite-groups-carry-regular-rank-models
requires:
  - locally-finite-hnn-data-allow-independent-cylinder-defects
artifacts:
  - research/artifacts/mismatched-factor-graph-of-groups-firewall-2026-09-12.md
---

Complete proof: artifact Section 1 (Theorem 1.1, Corollaries 1.2–1.3).

- **Stages.** Take finite subgraphs `Y_n` and finite subgroups `H_(n,v)` exhausting each vertex group, with
  `K_(n,e) = {k in K_e cap H_(n,v) : phi_e(k) in H_(n,w)}`.
- **Forest edges.** On a set of size `N_n = prod |H_(n,v)|`, start from a free action of a root group and extend
  leaf by leaf. Along an edge, the given free `K_(n,e)`-set and any free `H_(n,w)`-set restricted along `phi_e` are
  free with the same number of orbits, hence isomorphic, and transporting the `H_(n,w)`-action makes the two agree
  on `K_(n,e)`.
- **Other edges.** Match orbits of `K_(n,e)` and `phi_e(K_(n,e))` to get a permutation intertwiner, as for HNN
  letters.
- **Limit.** The ultraproduct satisfies every vertex relation and every edge relation exactly at large stages, so
  it is a homomorphism of `pi_1(Y)`.
- **Ranks.** Free `Q`-sets give the free profile. Fixed vectors of an infinite vertex group have rank at most
  `1/|H_(m,v)|`.
- **Weak finiteness.** Each `M_k(M)` is again a rank ultraproduct, and `rank(I - AB) = rank(I - BA)` at every finite
  stage, so a one-sided inverse is two-sided.
- **Defects.** Disjoint unit root configurations in one vertex group span `D_8 x ... x D_8`. The `F_2[D_8]` counts
  `4/8` and `3/8` from `locally-finite-hnn-data-allow-independent-cylinder-defects` give `3/8` and `(3/8)^k`.
