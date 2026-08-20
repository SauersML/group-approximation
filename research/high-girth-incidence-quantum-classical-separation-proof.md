---
rg: 2
id: high-girth-incidence-quantum-classical-separation-proof
kind: route
title: Combine incidence balance with small-cancellation phase survival
target: high-girth-incidence-gives-uniform-quantum-classical-separation
requires:
  - slofstra-zhang-high-girth-phase-survival
  - solution-group-central-order-is-operator-solvability
---

Choose an orientation of `G`.  Every column of `I(G)` contains one `+1` and
one `-1`, so the all-ones row vector kills `I(G)` and classical solvability
forces `sum b=0`.  If that sum vanishes, eliminate leaves of a spanning tree
to assign edge variables and solve the system.

The incidence hypergraph is `G` itself and its nonzero coefficients are
units modulo `p`.  Apply the Slofstra--Zhang theorem to obtain full order `p`
for the central phase for every `b`, then apply the central-order/operator-
solution equivalence.  Taking `sum b!=0` gives the announced separation.
