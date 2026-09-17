---
rg: 2
id: fpbs-bernoulli-cluster-indistinguishability
kind: claim
title: Infinite Bernoulli clusters on a Cayley graph cannot be told apart by any diagonally invariant property of the pair of cluster and configuration
distinct_from:
  fpbs-hp-uniqueness-and-long-range-order: that is the uniqueness versus long-range order equivalence along a subgroup; this is the indistinguishability theorem itself, for properties of the pair (cluster, configuration).
  fpbs-cluster-count-trichotomy: that fixes the number of infinite clusters; this says the infinite clusters, when there are several, share every invariant property.
---

**ESTABLISHED (imported).** Let `G` be a Cayley graph of a finitely generated
group `Gamma`, acting on `G` by left multiplication, and let `omega` be
Bernoulli(`p`) bond percolation, `p in (0,1)`. Let
`A subset 2^V(G) x 2^E(G)` be measurable and invariant under the diagonal
action of `Gamma`. Then almost surely either `(C, omega) in A` for every
infinite cluster `C` of `omega`, or `(C, omega) notin A` for every infinite
cluster `C`.

This is Lyons--Schramm, *Indistinguishability of percolation clusters*
(Ann. Probab. 27 (1999)), the Cluster Indistinguishability theorem of their
Section 3 together with their definition of indistinguishable infinite
clusters (source labels `t.cerg`, `d.inds`), for the insertion-tolerant `Gamma`-invariant process
Bernoulli(`p`). The acting group `Gamma` is discrete, hence closed and
unimodular, and transitive on vertices.

Status records an imported theorem, not independent mathematical verification.

DERIVATION
fpbs-bernoulli-cluster-indistinguishability-cite
