---
rg: 2
id: fpbs-hp-condensation-bernoulli-exit
kind: claim
title: The Hutchcroft--Pete condensation leaves the Bernoulli weak-containment closure either at its frequency stage, giving Bernoulli cost at most 1+|S|p/2, or at a zero-frequency non-hyperfinite stage
distinct_from:
  fpbs-kazhdan-ergodic-percolation-disagreement-floor: that is the Kazhdan lower bound on neighbour disagreement for ergodic percolation; here the relevant bound is the spectral-radius bound for all nonamenable groups inside W_b, together with the frequency and hyperfiniteness exit criteria and the cost transfer.
  fpbs-sparse-spine-cost-bound: that bounds cost from one FIID connected infinite vertex set; here the input is a weak limit of factors of iid with finitely many positive-frequency clusters and no selection of a cluster, and the output is the Bernoulli cost through monotonicity of cost under weak containment.
  fpbs-kazhdan-sparse-spines: that open target asks for FIID spines; this claim is a dichotomy for the Hutchcroft--Pete scheme run in the closure W_b.
---

**ESTABLISHED (written deduction over imported theorems; see the proof route).**

**Relation to earlier work.** The dead route `fpbs-dead-fiid-hutchcroft-pete-limit-recursion` keeps every stage a
factor of iid and dies because that class cannot reach the non-ergodic limit. This claim works in the weak-star closed
class `W_b` instead. It locates the exact stage where exact cluster thinning leaves `W_b`, and shows that leaving at
the frequency stage already gives Bernoulli cost near one.

**Setting.**
- `Gamma` is a finitely generated nonamenable group, `S` a finite symmetric generating set, `m` the uniform measure on
  `S`, and `rho = ||lambda(m)|| < 1` its spectral radius (Kesten).
- A site percolation is an invariant law `mu` on `{0,1}^Gamma`, and `b` is the Bernoulli shift `[0,1]^Gamma`.
- `W_b` is the set of site percolations `mu` whose shift, joined independently with `b`, is weakly contained in `b`.
  It contains every factor-of-iid percolation, and it is weak-star closed.
- For `p` in `(0,1)`, `q = (1 - sqrt(1-p))/p`, and `mu_i` is the Hutchcroft--Pete recursion (arXiv:1810.11015,
  Section 2.2): `mu_1` is Bernoulli(p), `mu^q` retains each cluster independently with probability `q`, and
  `mu_{i+1}` is the union of two independent samples of `mu_i^q`.
- `i_freq(p)` is their first stage with a cluster of positive frequency.
- `i_*(p)` is the first `i` with `mu_i^q` not in `W_b`. Every `mu_i` with `i <= i_*` lies in `W_b`.

**Theorem.**
- **(A) Spectral bound.** If `mu` is in `W_b` with marginal `p`, then
  `|sum_g m^{*n}(g) Cov_mu(omega(e), omega(g))| <= rho^n p(1-p)` for all `n`. Hence `i_*(p)` is finite for every
  nonamenable `Gamma` and every `p`. Explicitly, `i_*(p)` is smaller than the first stage whose average neighbour
  disagreement is below `2(1-rho)p(1-p)`.
- **(B) Frequency exit.** If `mu` is in `W_b` and has a positive-frequency cluster with positive probability, then
  `mu^q` is not in `W_b` for any `q` in `(0,1)`.
- **(C) Hyperfinite thinning stays.** If `mu` is in `W_b` and the cluster subrelation of the orbit relation of
  `mu x b` is hyperfinite, then `mu^q` is in `W_b`. More generally, thinning with coins constant on the classes of
  any hyperfinite Borel subrelation of the cluster relation stays in `W_b`. `W_b` is also closed under taking the
  union of independent samples.
- **(D) Cost transfer.** If `mu` is in `W_b` and has positive-frequency clusters with positive probability, then
  `C(b_Gamma) <= C(mu x b) <= 1 + E_mu[deg_omega(e)]/2 <= 1 + |S|p/2`.
  No cluster is selected. All maximal-frequency clusters are joined by a Borel set of cross edges of arbitrarily
  small measure.
- **(E) Dichotomy.** For every `p`, exactly one of the following holds:
  - **(I)** `i_*(p) = i_freq(p)`. Then `C(b_Gamma) <= 1 + |S|p/2`.
  - **(II)** `i_*(p) < i_freq(p)`, including `i_freq = infinity`. Then `mu_{i_*}` is an ergodic process in `W_b`
    with no positive-frequency cluster and a non-hyperfinite cluster relation.

**Consequences.**
- **Reduction (one direction).** Let `Gamma` be an infinite Kazhdan group, so that `i_freq(p)` is finite by
  Hutchcroft--Pete. If alternative (I) holds for arbitrarily small `p`, then `C(b_Gamma) = 1`. By Abert--Weiss
  maximality, `Gamma` then has fixed price one.
  - A sufficient condition is that the cluster relation of `mu_i` is hyperfinite for every `i < i_freq(p)`.
  - The converse is not proved: `C(b_Gamma) = 1` does not obviously force alternative (I).
- **Obstruction.** Every failure of the exact-thinning scheme to run inside the Bernoulli closure happens at a stage
  that is ergodic, has zero frequency and has a non-hyperfinite cluster relation. Such a stage is a
  nonuniqueness-type phase, since condensation has not yet happened.
  - It cannot happen at a hyperfinite stage, by (C).
  - It cannot happen after the frequency stage, by (B).
  - When `C(b_Gamma) > 1` it must happen for all `p < 2(C(b_Gamma)-1)/|S|`, by (D).
- **Calibration.**
  - For the free group `F_r` with standard generators, `C(b) = r`, so alternative (II) is forced for
    `p < 1 - 1/r`. This is consistent with (A)-(D).
  - For amenable `Gamma`, `rho = 1`, every free action is weakly equivalent to `b`, `W_b` is everything, and nothing
    exits. This is consistent with fixed price one there.
