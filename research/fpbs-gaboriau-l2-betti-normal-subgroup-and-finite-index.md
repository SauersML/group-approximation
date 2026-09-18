---
rg: 2
id: fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index
kind: claim
title: First L2 Betti numbers of countable groups vanish over an infinite normal subgroup of infinite index with finite first Betti number, and are multiplicative under finite index
distinct_from:
  fpbs-finite-cost-normal-subgroup-infimal-cost-one: that imports the cost statement (Gaboriau 2002 Theorem 3.4) that finite cost of the normal subgroup forces infimal cost one; this imports the L2 statement Theorem 6.8, whose hypothesis is finiteness of beta_1 of the normal subgroup, and the finite-index multiplicativity formula.
  fpbs-amen2-betti-cost-input: that imports the inequality beta_1 <= C - 1; this imports the normal-subgroup vanishing theorem and the index formula.
  l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup: that needs an amenable normal subgroup and gives all degrees; this allows any infinite normal subgroup of infinite index with finite beta_1, in degree one.
---

Imported published result. Let `Gamma` be a countable group and `beta_1` its first
L2-Betti number in the sense of Gaboriau.

- **(a) Normal subgroups.** If `1 -> N -> Gamma -> Lambda -> 1` is exact, `N` and `Lambda` are infinite, and
  `beta_1(N) < infinity`, then `beta_1(Gamma) = 0`.
- **(b) Finite index.** If `Lambda` has finite index in `Gamma`, then
  `beta_n(Lambda) = [Gamma : Lambda] beta_n(Gamma)` for every `n`.

This is a citation import (D. Gaboriau, Publ. Math. IHES 95 (2002), Theorem 6.8 and the table of properties in
Section 1), not a reproof. See the citation route.
