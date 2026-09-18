---
rg: 2
id: fpbs-unique-cluster-forces-higher-filling-density
kind: claim
title: A unique infinite cluster of density theta must carry k-cell filling density at least (k+1) beta_k
distinct_from:
  fpbs-amen2-betti-cost-input: that is Gaboriau's first-degree inequality beta_1 <= cost - 1 for a free action; this is a degree-k statement for the infinite-cluster subrelation under uniqueness, combining the induction formula with Morse inequalities for (k-1)-connected cluster complexes.
  fpbs-non-fixed-price-one-has-nonuniqueness: that uses cost or beta_1 and is blind for fixed-price-one groups such as F_2 x F_2; this lower bound is nonzero whenever some beta_k with k >= 2 is positive.
  fpbs-fixed-price-one-percolation-kernel: that is the open strict-threshold claim for fixed-price-one groups, whose cost bound reads 0 <= 0 under collapse; this is an established consequence of collapse that stays strictly positive on the subclass beta_k > 0 with k >= 2.
---

**ESTABLISHED** (via `fpbs-unique-cluster-forces-higher-filling-density-proof`,
a deduction from verbatim-cited theorems of Gaboriau 2002).

**Setting.** Let `Gamma` be an infinite finitely generated group and `G` a
locally finite Cayley graph of `Gamma` with base vertex `o`. Let `P` be a
`Gamma`-invariant bond percolation on `G`, realized as a free p.m.p. action
of `Gamma` on `(Omega, mu)`. Bernoulli bond percolation with `p` in `(0,1)`
is such an action. Otherwise take the product with an independent Bernoulli
coordinate. Put `Omega_inf = {omega : o in an infinite cluster}` and
`theta = mu(Omega_inf)`.

Call a field `omega -> Psi_omega` **admissible in degree k** (`k >= 1`) if:

- `Psi_omega` is a simplicial complex whose vertex set is the union of the
  infinite clusters of `omega`, and each of its connected components is the
  vertex set of one infinite cluster;
- it depends measurably and `Gamma`-equivariantly on `omega` (with extra
  independent randomness allowed);
- each component is `(k-1)`-connected;
- for `i = 0, ..., k` the expected number of `i`-simplices of `Psi_omega`
  containing `o`, on the event `Omega_inf`, is finite.

Edges of `Psi` need not be edges of `G`.

**Statement.** Assume that `P`-a.s. there is exactly one infinite cluster.
Then every field admissible in degree `k` satisfies

```text
E[ #{k-simplices of Psi_omega containing o} ; o in K_inf ]  >=  (k+1) beta_k^(2)(Gamma).
```

Write `F_k(P)` for the infimum of the left side over admissible fields.
Under uniqueness, `F_k(P) >= (k+1) beta_k^(2)(Gamma)` for every `k >= 1`.

**Why it matters.** For `k >= 2` the bound does not shrink with `theta`. So
if `beta_k^(2)(Gamma) > 0` for some `k >= 2`, any sequence of unique
clusters with `theta -> 0` must keep an order-one density of filling
`k`-cells. This covers `F_2 x F_2`, surface groups x surface groups, and
irreducible lattices in `SL_2(R) x SL_2(R)`, all of which have
`beta_2 > 0` and `beta_1 = 0`. On the product groups, which have fixed price
one, the cost bound gives only `0 <= 0`
(`fpbs-fixed-price-one-percolation-kernel`). The use of this bound
is `fpbs-positive-higher-l2-betti-via-filling-density`.

**Calibration k = 1.** Take `Psi` = the cluster graph. The bound reads
`theta * E[deg_K(o) | o in K_inf] >= 2 beta_1(Gamma)`, so
`theta >= 2 beta_1 / d`. As `p` decreases to `p_c`, Bernoulli `theta(p)`
tends to `0` (right-continuity of `theta` and `theta(p_c) = 0`, BLPS). So
uniqueness fails just above `p_c`. This recovers the known theorem
`beta_1 > 0 => p_c < p_u`. For `k >= 2` the cluster graph is not simply
connected, and the fill is where all the difficulty lies.
