---
rg: 2
id: uniqueness-phase-cluster-relations-inherit-nonsoficity
kind: claim
title: Above p_u the Bernoulli cluster relation of a nonsofic group is nonsofic
distinct_from:
  kun-thom-free-nonsofic-action: that is a nonsofic free action of a residually finite (sofic) group, produced by compression rigidity; this is the inheritance of nonsoficity by percolation cluster subrelations of the Bernoulli shift of a group that is already nonsofic, with no rigidity input.
  fpbs-cluster-count-trichotomy: that is the imported uniqueness of the infinite cluster above p_u; this uses it to identify the cluster relation with a restriction of the orbit relation.
artifacts:
  - research/artifacts/percolation-soficity-threshold-2026-09-12.md
---

**Theorem.** Let `G` be finitely generated with finite symmetric generating set `S`. Let `G` act by the
Bernoulli shift on `Omega = [0,1]^E` over the edges of `Cay(G,S)`; this action is essentially free and
ergodic. Let `R_p ⊆ R_G` be the cluster relation of bond percolation `omega_p(e) = 1{xi(e) <= p}`, and
`A_p = { |cluster of 1| = infinity }`. For every `p in (p_u, 1]`:

1. `R_p|_(A_p) = R_G|_(A_p)` almost everywhere;
2. if `G` is not sofic, `R_p` is not sofic;
3. if `G` is not hyperlinear, `R_p` is not hyperlinear.

**Proof** (artifact, Sections 1--2).
- **Item 1.** By `fpbs-cluster-count-trichotomy` there is one infinite cluster, so two roots in infinite
  clusters lie in the same cluster.
- **Item 2.** `mu(A_p) = theta(p) > 0`. Suppose `R_p` were sofic.
  - Its restriction `R_G|_(A_p)` would be sofic (a corner of the embedding, with the permutations
    corrected on `o(n)` points).
  - `R_G` would be sofic, by amplification along finitely many partial isomorphisms into `A_p`, which
    exist by ergodicity.
  - `G` would be sofic: `tau(u_g) = mu(Fix g) = 0` makes `g -> Theta(u_g)` a sofic representation.
- **Item 3.** The same argument with `R^omega` embeddings.

**Scope.** This is a restriction-and-amplification argument, standard in the orbit-equivalence theory of
percolation. The only new point is that it applies to a nonsofic group. The labeled cluster network by
itself is a factor of `R_p`, and nothing here says that factor is nonsofic near `p_u`.
