---
rg: 2
id: fpbs-bs-positive-higher-l2-betti
kind: claim
root: true
title: Groups with a positive l2-Betti number in degree at least two have strict thresholds on every Cayley graph
distinct_from:
  fpbs-non-fixed-price-one-has-nonuniqueness: that covers beta_1 > 0 or cost > 1 through degree-one cost bounds; this is the degree >= 2 class, which contains fixed-price-one groups with beta_1 = 0 such as F_2 x F_2, where those bounds read 0 <= 0.
  fpbs-product-every-generating-set: that is the direct-product class H x K with every generating set; this is the class beta_k^(2) > 0 for some k >= 2. The two overlap on F_2 x F_2 and surface x surface groups, but this class omits F_2 x Z (all beta_k = 0) and includes irreducible lattices in SL_2(R) x SL_2(R), which are not products.
  fpbs-fixed-price-one-percolation-kernel: that is the whole fixed-price-one class; this is the subclass certified by a nonzero higher l2-Betti number, which gives a nonvanishing invariant to compress onto the infinite cluster.
---

**OPEN.** Let `Gamma` be an infinite finitely generated group with
`beta_k^(2)(Gamma) > 0` for some `k >= 2`. Then every locally finite Cayley
graph of `Gamma` has `p_c < p_u`.

Examples:

- `F_m x F_n` with `m, n >= 2` (`beta_2 = (m-1)(n-1)`);
- products of two closed surface groups;
- irreducible lattices in `SL_2(R) x SL_2(R)`.

All of these have `beta_1 = 0`. For the lattice this follows from
proportionality with a product of surface groups, [G02, Corollaire 0.2].
The two products have fixed price one, being direct products of infinite
groups. So Lyons' theorem does not reach them. For `F_2 x F_2` this is Choi-Seo's question, recorded on
`fpbs-product-every-generating-set`.

The proposed decomposition is `fpbs-positive-higher-l2-betti-via-filling-density`.
It rests on:

- the established lower bound `fpbs-unique-cluster-forces-higher-filling-density`;
- the open geometric hole `fpbs-near-critical-cluster-filling-density-vanishes`;
- the established reduction `fpbs-nonuniqueness-parameter-criterion`.

## Attempts

* **Higher l2-Betti compression onto the unique cluster (this lane, 2026-09-17).**
  - Result: collapse forces every `(k-1)`-connected filling of the unique
    cluster to have `k`-cell density `>= (k+1) beta_k`. This is established.
  - Therefore BS for this class follows from H_k.
  - **Where it stops:** H_k is open. The only step not covered is filling
    `pi_1` (for `k = 2`) of a near-critical Bernoulli cluster at vanishing
    cost. Generic projection fillings are blind to percolation, and sparse
    unique invariant percolations must violate the analogue. See the Attempts
    of the hole.
