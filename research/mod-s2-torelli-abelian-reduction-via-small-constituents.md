---
rg: 2
id: mod-s2-torelli-abelian-reduction-via-small-constituents
kind: route
title: A small prime-to-three Torelli constituent bounds the tensor-word loss, and the dichotomy turns it into a Torelli-abelian approximant
target: mod-s2-near-scalar-reps-reduce-to-torelli-abelian
requires:
  - mod-s2-cube-root-reps-have-small-prime-to-three-constituents
  - mod-s2-small-constituents-collapse-to-torelli-abelian-reduction
---

**Route (open because (SB) is open).** Assume `1/3 in Z_hon`.

1. By `mod-s2-cube-root-reps-have-small-prime-to-three-constituents` (SB), there are honest `rho_j` with
   Torelli constituents `W_j` such that `3 not| dim W_j` and `dim W_j * arcsin(eps_j/2) -> 0`. OPEN.
2. By (C1) of `mod-s2-small-constituents-collapse-to-torelli-abelian-reduction`, `dim W_j * eps_j >= c_ab`.
   Hence `c_ab = 0`, which means `1/3 in Z_ab`. ESTABLISHED.

The converse, that the target implies (SB), is (C2) of the same node. It is not filed as a route, so the graph
stays acyclic. So this route and the target have the same open content. The route records that the
small-constituent formulation is not a weaker entry point to the target.
