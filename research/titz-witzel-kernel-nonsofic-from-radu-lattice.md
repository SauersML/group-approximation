---
rg: 2
id: titz-witzel-kernel-nonsofic-from-radu-lattice
kind: route
title: A nonsofic Radu BMW lattice makes the Titz--Witzel kernel nonsofic
target: titz-witzel-kernel-nonsofic
requires:
  - radu-bmw-lattice-nonsofic
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - sofic-kernel-amenable-quotient-permanence
---

Suppose `Gamma_R` is not sofic.  Then its index-four normal subgroup
`pi_1(S_R)` is not sofic, since otherwise
`sofic-kernel-amenable-quotient-permanence` would make `Gamma_R` sofic.
`pi_1(S_R)` is a subgroup of `K = Gamma_1^2`, and subgroups of sofic groups
are sofic.  So `K` is not sofic.

The attack this route opens needs no property `(T)` and no building
geometry.  It lives entirely in a lattice on a product of two trees, whose
four-involution presentation is displayed in `radu-bmw-lattice-sofic`.
