---
rg: 2
id: fpbs-tree-projected-via-critical-sphere-bubble
kind: route
title: A critical fibre-sphere bubble below one gives the L2 gap, hence strict thresholds
target: fpbs-tree-projected-cayley-graphs-strict-thresholds
requires:
  - fpbs-tree-projected-sphere-bubble-l2-equivalence
  - fpbs-tree-projected-critical-sphere-bubble-below-one
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Fix a tree-projected generating set `S`.
1. The premise gives `R` with `b_R(p_c) < 1`.
2. The equivalence claim then gives `p_c < p_{2->2}` on `Cay(Gamma,S)`.
3. Hutchcroft arXiv:1804.10191 Section 2 gives `p_{2->2} <= p_u`, since
   uniqueness forces `inf tau_p >= theta(p)^2` and unbounded `T_p`.
4. Hence `p_c < p_u`.

This is not a restatement. The premise concerns one finite sphere of the free
quotient at criticality, while the target is a threshold gap for the whole
graph.
