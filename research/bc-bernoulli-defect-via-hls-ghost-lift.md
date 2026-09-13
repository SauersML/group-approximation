---
rg: 2
id: bc-bernoulli-defect-via-hls-ghost-lift
kind: route
title: A full-shift class with ghost ranks on marked expanders and vanishing tree-boundary part makes the Bernoulli cylinder comparison non-surjective
target: bernoulli-cylinder-comparison-fails-for-some-group
requires:
  - hls-ghost-class-lifts-to-the-bernoulli-full-shift
  - hls-ghost-lift-needs-forest-shift-failure
---

**Live.** Suppose `hls-ghost-class-lifts-to-the-bernoulli-full-shift` holds. Then there are:
- a prime `p`;
- a torsion-free host `G` satisfying (M) and (H-K);
- a class `y ∈ K_0(C_0((Z/p)^G \ {0}) ⋊_r G)` with `y|_(∂Y) = 0` and `r_(x_n)(y) ≠ 0` infinitely often.

Item 1 of `hls-ghost-lift-needs-forest-shift-failure` gives `y ∉ im T_r`, with `Z = G` a free `G`-set. That is the target.
