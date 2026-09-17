---
rg: 2
id: fpbs-percolation-kesten-normal-gap
kind: claim
title: Percolation Kesten criterion, a normal subgroup with nonamenable quotient has a strictly larger relative threshold
distinct_from:
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that proves the statement on the free-group tree, where the relative threshold is the inverse cogrowth; this asserts the strict gap on every Cayley graph of every group.
  fpbs-hyperbolic-quotient-every-generating-set: that is the gap for groups with a non-elementary hyperbolic quotient; this is one percolation statement for every nonamenable quotient, and it implies that claim through the separation criterion.
  fpbs-amenable-wq-normal-relative-subcriticality: that asks for finite relative susceptibility along an amenable wq-normal subgroup; this asks for the threshold gap along any infinite normal subgroup, amenable or not, provided the quotient is nonamenable.
  fpbs-relative-gap-along-any-subgroup-separates: that turns a relative gap into p_c < p_u; this is the proposed universal source of such gaps.
---

**OPEN.** Let `Gamma` be finitely generated, and let `N` be an infinite normal
subgroup such that `Gamma/N` is nonamenable. Then for every finite symmetric
generating set `S`, with `G = Cay(Gamma,S)`,

```text
p_c(G) < p_c(N;G).
```

This is the percolation analogue of the Kesten--Grigorchuk cogrowth criterion,
which says that simple random walk returns to `N` with exponentially small
probability iff `Gamma/N` is nonamenable.

**What it would give.** Combined with `fpbs-relative-gap-along-any-subgroup-separates`,
it gives `p_c < p_u` on every Cayley graph of every group that has an infinite
normal subgroup with nonamenable quotient. That class contains:

* every nonamenable direct product `H x K` of infinite groups, taking `N = K`
  (`fpbs-product-every-generating-set`), including `T x T'` for Tarski monsters
  and `B(m,n) x B(m',n')`;
* every group with an infinite normal subgroup and non-elementary hyperbolic
  quotient (`fpbs-hyperbolic-quotient-every-generating-set`);
* every nonamenable group with an infinite amenable normal subgroup, since
  then the quotient is nonamenable.

**Evidence.**

1. **Trees.** On the free-group tree `p_c(N;T)` is the inverse cogrowth of
   `N`, and the gap holds iff `Gamma/N` is nonamenable
   (`fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`).
2. **Mean field.** Slightly supercritical clusters look like critical branching
   random walk, and the projection of branching random walk with mean `m` to
   `Q = Gamma/N` visits the identity fibre finitely often in expectation iff
   `m rho(Q) < 1`. We have `rho(Q) < 1` exactly when `Q` is nonamenable, so
   near `m = 1` the fibre occupation is finite.
3. **Uniform fibres.** Below `p_c(N;G)` the cluster mass on every fibre is
   uniformly bounded (`fpbs-normal-fibre-second-moment-maximal`). In a gap
   window the infinite susceptibility is spread across infinitely many fibres,
   as branching random walk transience predicts.

**Converse direction, not claimed.** If `Gamma/N` is amenable and `N` is
nonamenable, one expects `p_c(N;G) = p_c(G)`. No proof is known, and neither
direction is used here.

## Attempts

* **BK coset-walk bound.** Split `S = S_in ∪ S_out` with `S_in = S ∩ N`. Edges
  labelled by `S_in` stay in a coset, and edges labelled by `S_out` move the
  projection to `Q = Gamma/N`. Cut an open path at its `S_out` steps and apply
  the BK inequality. With `chi_in(p)` the susceptibility of percolation on the
  fibre graph spanned by `S_in` and `mu_out` the uniform measure on the image of
  `S_out` in `Q`, this gives

  ```text
  chi^N_p <= chi_in(p) sum_n (p chi_in(p) |S_out|)^n mu_out^{*n}(e_Q),
  ```

  which is finite when `p chi_in(p) |S_out| rho(Q,mu_out) < 1`.
  **Where it dies:** the certified window has to reach above `p_c(G)`, and the
  bound gives no matching upper bound on `p_c(G)` in terms of the same
  quantities. As `p` increases, `chi_in(p)` blows up at the fibre threshold,
  while `p_c(G)` sits strictly below it. So the criterion certifies a gap only
  in product-like regimes where `S_out` dominates, and gives nothing for
  general `S`.
* **L2 threshold.** Hutchcroft's `p_c < p_{2->2}` would control `chi^N` only
  through the fibre-summed kernel
  `T^Q_p(qN, q'N) = sum_{n in N} tau_p(q, q'n)` on `l2(Q)`. For positive kernels
  the quotient norm dominates the group norm, as with Kesten's
  `rho(Gamma) <= rho(Q)`, and it strictly exceeds it in the random-walk case
  when `N` is nonamenable. **Where it dies:** boundedness of `T_p` on `l2(Gamma)`
  does not bound `T^Q_p`. For amenable `N` the two agree, and this is the
  amenable-kernel reduction already recorded in
  `fpbs-hyperbolic-quotient-every-generating-set`. For nonamenable `N`,
  bounding `T^Q_p` above `p_c` is the claim itself.
* **Uniform fibres (partial).** `fpbs-normal-fibre-second-moment-maximal`
  bounds all fibre masses by the identity fibre below `p_c(N;G)`. **Where it
  stops:** this is a consequence of the gap, not a route to it. It rules out
  single-fibre concentration in a gap window but does not create one.
