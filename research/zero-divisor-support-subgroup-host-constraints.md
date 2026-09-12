---
rg: 2
id: zero-divisor-support-subgroup-host-constraints
kind: claim
title: A zero divisor over a torsion-free group lives in a finitely generated subgroup without unique products that is not elementary amenable
distinct_from:
  strong-atiyah-torsion-free: that is the integrality conjecture; this records which properties of the support subgroup a zero divisor must violate, integrality in characteristic zero among them.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is an established necessary condition on any counterexample.
---

**ESTABLISHED.** Let `G` be torsion-free, let `k` be a field, and let `alpha`
and `beta` be nonzero elements of `k[G]` with `alpha beta = 0`. Put
`H = <supp alpha ∪ supp beta>`. Then:

1. `H` is a finitely generated torsion-free group, and `alpha beta = 0`
   already holds in `k[H]`;
2. `H` does not have unique products;
3. `H` is not elementary amenable;
4. if `char k = 0`, then `H` does not satisfy the Strong Atiyah conjecture
   over `C`.

So a counterexample host must be torsion-free, must lack unique products, and
must not be elementary amenable. In characteristic zero it must also violate
Strong Atiyah. Positive characteristic removes only condition 4.
