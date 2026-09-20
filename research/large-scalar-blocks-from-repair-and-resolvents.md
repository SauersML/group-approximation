---
rg: 2
id: large-scalar-blocks-from-repair-and-resolvents
kind: route
title: "Couple relative repair, monotone selection, in-place rounding and pruning"
target: quotient-gap-gives-large-scalar-expanding-blocks
requires: [quotient-gap-gives-uniform-relative-projection-repair, low-energy-povms-round-equivariantly-in-place, resolvent-assembly-controls-covariance-and-leakage, defective-block-expansion-prunes-to-doubled-gaps]
artifacts:
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 5.1, using Theorems 3.2 and 4.3 and Lemmas 5.2–5.4. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

Use the common repair corner e_n and its eta_n before selecting any seed. At fixed small t, choose a minimum-rank p_i in a high-density window of (I+lambda S_(i-1))^(-1) satisfying E(p_i)+3 tr(p_i(1-e_n))<beta tr(p_i), and repair it to f_i. The positive resolvent increments telescope; the logarithmic determinant potential bounds total repaired rank and partition purity.

Apply in-place equivariant rounding to the positive increments and final remainder. For each resulting physical block construct Y_i=g(D_(i-1))B_i Q_i and its cut-down polar part V_i. Localized covariance gives sum_i E(V_i)->0; the monotone-chain estimate gives sum_i tr(V_i V_i^*(1-e_n))->0. Although ranges need not be orthogonal, initial supports are. Every half-rank test in a physical block transports into its original minimum-rank selection window. Thus ALL such tests obey expansion with additive defects xi_i whose SUM tends to zero.

Pruning costs O(sum xi_i/beta), hence vanish at fixed t. Choose t to make the remaining discarded fraction <=epsilon. This is the assembly in Liu Theorem 5.1; the cited audit records equations (5.17)-(5.41), the determinant potential and the order of limits. This conditional route does not establish any of its analytic prerequisites.
