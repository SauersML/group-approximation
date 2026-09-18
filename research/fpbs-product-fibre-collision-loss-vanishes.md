---
rg: 2
id: fpbs-product-fibre-collision-loss-vanishes
kind: claim
title: On a nonamenable factor times a high-degree factor, the inter-fibre collision loss of the fibre-renormalized branching falls below the spectral margin of the nonamenable factor
distinct_from:
  fpbs-product-amenable-factor-mean-field-deficit: that asks for the whole-graph deficit d-1-1/p_c to vanish, which fails at order one for spread-out factors because of their own triangles (computation in fpbs-fibre-renormalized-nonbacktracking-certificate); this asks only that fibre clusters, contracted to their susceptibility, rarely collide across H-steps, a quantity in which the cycles of the factor B do not appear.
  fpbs-fibre-renormalized-nonbacktracking-certificate: that proves the certificate and the dichotomy a counterexample must satisfy; this is the open inequality that would refute the dichotomy on high-degree products.
  fpbs-percolation-kesten-normal-gap: that asks for a relative gap along every normal subgroup on every generating set; this is one asymptotic inequality on products, for the normal factor B only.
---

**OPEN.**

**Setting.** Let `(H,S_H)` be finitely generated with `d_H = |S_H|` and
`delta_H = d_H - ||A_H|| > 0`. Let `(B_k,S_k)` be infinite finitely generated
groups with `d_k = |S_k| -> infinity`, and put
`G_k = Cay(H,S_H) □ Cay(B_k,S_k)`.

For `p < p_c(B_k)` define, as in Corollary C of
`fpbs-fibre-renormalized-nonbacktracking-certificate`:

* `chi = chi_(B_k)(p)` and `gamma = 1/chi`;
* `kappa_p = 1/(p chi)`;
* `L_p = d_H - gamma - kappa_p`.

**Claim.** For all large `k` there is `p ∈ (p_c(G_k), p_c(B_k))` with

```text
L_p + gamma  <  delta_H     and     p d_H  <=  kappa_p.                (*)
```

**Consequence.** Condition (*) negates both alternatives of Corollary C(2).
The first alternative fails because `delta_H - gamma + p(d_H - gamma) >= delta_H - gamma > L_p`.
The second fails because `p(d_H - gamma) < p d_H <= kappa_p`. Hence
`p_c(G_k) < p_u(G_k)` for all large `k`, and for every nonamenable `H`,
including Kazhdan and torsion `H`.

This would kill the class "nonamenable times a high-degree factor" for every
choice of `S_H`. It would also do so for factors `B_k` whose own short cycles
make `D(G_k)` of order one, such as spread-out balls, which the deficit route
cannot reach.

A convenient sufficient asymptotic form: at some `p_k` in the interval,

```text
L_(p_k) -> 0,     chi_(B_k)(p_k) -> infinity,     p_k -> 0,
```

with `kappa_(p_k)` bounded below.

**What `L_p` measures.** By Corollary C(1), `L_p >= 0` above `p_c(G_k)`. The
BK bound of the certificate treats every visit of the explored cluster to a
fibre `hB_k` as a fresh fibre cluster of mean size `chi`. `L_p` is the amount
by which this overcounts the true renormalized branching at criticality.
Overcounting happens only when a later visit to the same fibre lands in an
earlier fibre cluster. There are two ways:

* two parallel `s`-edges from one fibre cluster enter the same fibre cluster
  of `hsB_k`;
* an `H`-word of length `ell` returns to `hB_k` (a backtrack or a cycle of
  `X`), and its fibre displacement lands in the earlier cluster.

The cycles of `B_k` appear in neither case; they are inside `chi`.

**Heuristic.** A tree-graph count of the first case gives a relative loss of
about `p (nabla_B(p) - 1)` per label, where `nabla_B(p) = sum_w tau_B(o,w)^2`.
The second case gives `t^ell` times open bubbles of `tau_B^{*ell}` against
`tau_B`, normalised by `chi^ell`. So

```text
L_p  ≈  d_H p (nabla_B(p) - 1) + sum_ell (#returning H-words of length ell) (relative ell-bubble).
```

Near `p_c(G_k)` one has `p ≈ 1/d` and `chi_B ≳ 1/(p d_H)`.

* **Large `d_k` with bounded bubble** (`Z^k`, spread-out balls in high
  dimension): all terms are `O(d_H/d)`, so `L -> 0`.
* **Spread-out range `k` in `Z` or `Z^2`:** the bubble grows, but as a power
  of `k` smaller than `d_k`, so `p nabla_B -> 0` should still hold.

## Attempts

**Where it can fail on its own.**

* **Margin near the factor's threshold.** No upper bound on
  `chi_(B_k)(p_c(G_k))` is known. If `p_c(G_k)` is within `o(1/d_k^2)` of
  `p_c(B_k)`, then `nabla_B` can be of order `chi^2/volume`, and `p nabla_B`
  need not vanish. Theorem B gives only the lower bound `chi >= 1/(p d_H)`.
* **Low-dimensional factor.** For `B_k` of fixed small growth and bounded
  degree the heuristic fails. That regime is excluded here by `d_k -> infinity`.
* **No lace expansion.** Making the tree-graph heuristic rigorous at `p_c(G_k)`
  needs a triangle-type bound for `G_k` itself, as in the lace expansion. On
  nonamenable `G_k` this has to be done with operator norms rather than
  Fourier transforms.

**Status of the calibration (2026-09-17, swarm-0917 w5 heretic).**

* `F_2 × Z` with range `k` is a Cartesian product with a tree factor. It has
  `p_c < p_u` by nonunimodularity, so it tests the inequality, not the thresholds.
* No rigorous upper bound on `L_p` has been computed. The script
  `experiments/fibre-renormalized-certificate-2026-09-17/saw_triangle_deficit.py`
  shows only that the unrenormalized deficit does not vanish for these graphs.
