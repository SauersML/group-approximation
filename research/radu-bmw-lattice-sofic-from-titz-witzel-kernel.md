---
rg: 2
id: radu-bmw-lattice-sofic-from-titz-witzel-kernel
kind: route
title: Restrict a sofic approximation of the Titz--Witzel kernel to the Radu subcomplex group
target: radu-bmw-lattice-sofic
requires:
  - titz-witzel-kernel-sofic
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - sofic-kernel-amenable-quotient-permanence
---

If `K = Gamma_1^2` is sofic, its subgroup `pi_1(S_R)` is sofic by restricting
the embedding into the metric ultraproduct of symmetric groups.  `Gamma_R`
contains `pi_1(S_R)` as a normal subgroup of index four.  Soficity passes to
extensions with finite, hence amenable, quotient
(`sofic-kernel-amenable-quotient-permanence`), so `Gamma_R` is sofic.

This is only a consequence, not an attack: the premise is the harder
statement.  It shows that the positive horn of the Titz--Witzel gate contains
the open soficity question for this BMW lattice.
