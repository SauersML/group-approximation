---
rg: 2
id: local-context-full-group-norm-limit-proof
kind: route
title: Extend finite partial unitaries and take a cyclic state limit
target: local-context-hierarchy-converges-to-full-group-norm
requires: []
artifacts:
  - research/artifacts/local-context-and-global-norm-hierarchies.md
---

Lemma 1 and Theorem 2 of the artifact supply the complete proof.
For any tuple $T$ and vector $\xi$, let $K_L$ span its word orbit through
length $L$. Extend $T_i$ from
$K_{L-1}+T_i^{-1}K_{L-1}$ to a unitary of $K_L$ by matching the orthogonal
complements of its domain and range. Both signs of each letter then agree
on $K_{L-1}$. This preserves all constraints and objective values at a
fixed level, proving the dimension bound and compact attainment.

Apply the same construction to arbitrary representations of $G$ to obtain
the lower bound by the full norm. For the upper bound, a weak-star limit of
maximizing vector states on $C^*(F_m)$ annihilates
$q^*(r-1)^*(r-1)q$ for every word $q$. In the GNS representation each
$r-1$ therefore kills a dense cyclic subspace and hence the whole space.
The representation factors through $C^*(G)$, proving equality in the limit.
The regular representation supplies the squared lower bound two for a
nontrivial word. This is a written proof, not a computational or Lean claim.
