---
rg: 2
id: fpbs-critical-profile-kesten-ratio-integrable
kind: claim
title: Over a nonamenable quotient the size-biased squared Kesten ratio of the cluster's fibre profile stays bounded up to p_c
distinct_from:
  fpbs-critical-sphere-fibre-operator-below-one: that is a bound on one annealed operator, the sphere-restricted critical fibre operator, and is equivalent to critical fibre l2; this is a quenched, per-cluster spectral statement about the finite profile a_K on Q, and it is strictly stronger than critical fibre l2, since the Gram bound is an inequality.
  fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2: that reduces the gap to ||sigma_(p_c)||_Q < infinity; this is a sufficient condition for that premise, stated cluster by cluster.
  fpbs-hutchcroft-l2-gap-criterion: that is p_c < p_(2->2) for the whole graph; the case N = {e} of this claim implies it, but the claim is posed only for infinite N with nonamenable Q.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is conjecture E, an equality of thresholds; this gives only the strict inequality p_c < p^Q_(2->2), and it is the input that the invariant-percolation type-(ii) witness shows cannot come from partition structure alone.
artifacts:
  - research/artifacts/fpbs-cluster-gram-fibre-operator-2026-09-17.md
  - experiments/fpbs-gram-profile-2026-09-17/tree_cluster_kesten_ratio.py
  - experiments/fpbs-gram-profile-2026-09-17/tree_cluster_power_lower_bound.py
---

**OPEN.**

*Setting.* Let `Gamma` be finitely generated, let `S` be a finite symmetric
generating set, and let `N` be an infinite normal subgroup with
`Q = Gamma/N` nonamenable.

- For the cluster `K_o` of Bernoulli(`p`) bond percolation on `Cay(Gamma,S)`,
  let `a(u) = |K_o ∩ u~ N|` be its fibre profile on `Q`.
- Let `r(a) = ||lambda_Q(a)||_(2->2) / ||a||_1` be the Kesten ratio of the
  profile, which lies in `(0,1]`.

*Claim.*

```text
limsup_{p ↑ p_c(G)}  E_p[ |K_o| r(a)^2 ]  =  limsup_{p ↑ p_c(G)}  E_p[ ||lambda_Q(a)||^2 / |K_o| ]  <  infinity.
```

**What it gives.** By item 4 of
`fpbs-normal-fibre-mass-cluster-gram-representation`, the claim gives
`||sigma_(p_c)||_Q < infinity`. By item 6 of
`fpbs-quotient-l2-threshold-sandwich`, that gives
`p_c < p^Q_(2->2)(N;G) <= p_c(N;G)`, which is the Kesten gap
`fpbs-percolation-kesten-normal-gap` on this Cayley graph (route
`fpbs-kesten-gap-via-profile-kesten-ratio`).

**Why this is a decomposition and not a restatement.**

- The Gram bound
  `||sigma_p||_Q <= E_p[ ||lambda_Q(a)||^2/|K_o| ]` is an inequality, not an
  identity. The supremum over test vectors sits outside the expectation.
- The claim asks for control of the shadow of each typical cluster on `Q`: the
  shadow must spread over `Q` nonamenably. It asks nothing of the averaged
  two-point function.
- It can fail independently of critical fibre l2. It fails whenever large
  critical clusters have amenable-like shadows with positive size-biased
  probability, even if the averaged operator stays bounded.

**Necessary features.** These are Sections 2 and 4 of the artifact.

- **Nonamenable `Q` is needed.** For amenable `Q`, `r = 1`, so the quantity
  equals `chi_p`, which tends to infinity. The claim is false there, as it must
  be.
- **Bernoulli input is needed.** A finite-cluster invariant partition of
  `F_2 x Z` has clusters confined to cosets of `<a>`. It has `chi^N = 1`, and the
  quantity is infinite, matching `||sigma||_Q = infinity`. So the claim cannot
  follow from invariance and partition structure. The proof must use something
  like Russo, BK, or insertion tolerance.
- **A rate is needed.** At `p_c` the volume tail is at least of order `n^(-1/2)`,
  by the classical Aizenman--Barsky bound (not re-verified here). Fatou's lemma
  passes the limsup to `E_(p_c)`. Suppose that for some `c > 0` a fixed positive
  fraction of clusters of each size `n` had `||lambda_Q(a)||^2 >= c n^(3/2)`,
  that is, `r(a) >= c^(1/2) n^(-1/4)`. Then the quantity would diverge like the
  harmonic series. So the claim forces the Kesten ratio of typical large
  critical profiles to decay faster than `|K|^(-1/4)`.

**Evidence.** Mean-field heuristics support the claim. For critical branching
random walk projected to a nonamenable `Q`, `||a||_2^2 = O(|K|)`, and the shadow
is tree-like and nonamenable.

Numerically, on the tree `T_3` (with `N` trivial, as a proxy), rigorous lower
bounds on `||lambda(1_K)||^2/|K|` grow only slowly with `|K|`. They are about 7
at `|K| ≈ 10`, 9 at `|K| ≈ 20` and 10.4 at `|K| ≈ 46`. The comparison value for
metric balls of the same size is larger: about 11 at `|K| = 22` and 16 at
`|K| = 46` (Section 4 of the artifact). These are lower bounds only, so they can
kill the claim but cannot confirm it. They show no sign of the forbidden
`|K|^(1/2)` growth.

**First killing test.** Take the one-ended case `F_2 x Z` with `N = Z` on its
standard generating set. Estimate `||lambda_(F_2)(a)||^2/|K|` for critical
clusters by the pruned power iteration of
`tree_cluster_power_lower_bound.py`, adapted to shadows. A lower bound growing
like `|K|^beta` with `beta >= 1/2` kills the claim there.
