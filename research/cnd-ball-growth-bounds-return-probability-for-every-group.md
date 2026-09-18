---
rg: 2
id: cnd-ball-growth-bounds-return-probability-for-every-group
kind: claim
title: The ball growth of any conditionally negative definite function bounds return probabilities from below
distinct_from:
  thompson-f-moment-data-cannot-certify-nonamenability: that concerns finitely many moments of the spectral measure of F; this is an inequality valid in every group, relating one cnd function to all return probabilities.
  thompson-f-cnd-certificates-need-near-exponential-ball-growth: that applies this inequality to F together with Moore's tower bound; this is the group-independent inequality.
---

**ESTABLISHED.** Let `G` be a countable group and `mu` a symmetric, finitely supported
probability measure on `G`. Let `X_n = s_1 ... s_n` be the right `mu`-random walk from `e`,
with law `u_n = mu^{*n}` and return probabilities `p_k = mu^{*k}(e)`. Let `psi : G -> [0, inf)`
be conditionally negative definite with `psi(e) = 0`. Put `c = E_mu psi = sum_s mu(s) psi(s)`
and `B_R = {g : psi(g) <= R}`.

1. **(Second moment.)** `E psi(X_n) <= n c` for every `n >= 0`.
2. **(Return probability.)** If `c > 0`, then for every `n >= 1`,
   `p_{2n} >= 1 / (4 |B_{2cn}|)`. If `B_{2cn}` is infinite, the bound is empty.

**Consequence (by Kesten's theorem, cited not re-proved).** Suppose `mu` generates `G`, the
balls `B_R` are finite, and `log |B_R| = o(R)`. Then `p_{2n}^{1/(2n)} -> 1`, so `G` is amenable.

Equivalently, if `e^{-t psi}` lies in `l^2(G)` for every `t > 0`, then `log |B_R| = o(R)`.
- *Why.* `|B_R| e^{-2tR} <= ||e^{-t psi}||_2^2`.
- *Converse.* It holds when the balls are finite: `sum_g e^{-2t psi(g)} <= sum_{j >= 0} |B_{j+1}| e^{-2tj}`.

This is the "Gaussian certificate" of amenability: an l^2 positive definite deformation of the
trivial character.

**Scope.**
- Novelty is not claimed. Item 1 is the Markov-type-2 inequality of Hilbert space, specialised
  to cocycles; item 2 is a Markov-inequality and Cauchy–Schwarz step.
- The graph records it because it is the input for the class kill in
  `thompson-f-cnd-certificates-need-near-exponential-ball-growth`.

Proof route: `cnd-ball-growth-return-probability-proof`.
