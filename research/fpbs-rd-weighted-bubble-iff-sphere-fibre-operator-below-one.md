---
rg: 2
id: fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one
kind: claim
title: Over a rapid-decay quotient the weighted critical fibre bubble is finite iff one sphere fibre operator has norm below one
distinct_from:
  fpbs-rd-quotient-weighted-bubble-gives-critical-l2: that bounds the critical connectivity operator by the weighted bubble; this shows the weighted bubble is equivalent to a single finite-radius operator norm, to a single sphere bubble below an explicit threshold, and to exponential decay of critical fibre tails.
  fpbs-sphere-cut-fibre-tails-decay-exponentially: that is the quotient-free bootstrap from one operator norm to exponential tail decay; this adds rapid decay, which gives the explicit sphere-bubble threshold and the converse directions.
  fpbs-rd-quotient-weighted-critical-fibre-bubble: that is the open weighted premise over hyperbolic quotients; this is the unconditional equivalence of that premise with single-radius conditions, which settles nothing about whether they hold.
artifacts:
  - research/artifacts/fpbs/docs/sphere-cut-fibre-bootstrap.md
---

**ESTABLISHED (equivalence).** Let `Gamma`, `S`, `H` and `Q = Gamma/H` be as in
`fpbs-sphere-cut-fibre-tails-decay-exponentially`. Suppose `Q` has rapid decay
with constants `C, D`: `||lambda(f)|| <= C (1+R)^D ||f||_2` for `f` supported in
`B_Q(R)`. On `Cay(Gamma,S)` the following are equivalent:

* **(a)** `W_D(p_c) = sum_q (1+|q|)^(2D+2) sigma_{p_c}(q)^2 < infinity`;
* **(b)** `C^2 (1+R_0)^(2D) b_{R_0}(p_c) < 1` for some `R_0 >= 1`, where
  `b_R = sum_{|q|=R} sigma^2`;
* **(c)** `||lambda_Q(sigma_{p_c} 1_{S_Q(R_0)})||_{2->2} < 1` for some `R_0 >= 1`;
* **(d)** the critical fibre tails `sum_{|q|>=m} sigma_{p_c}(q)^2` decay
  exponentially in `m`;
* **(e)** `sum_q (1+|q|)^s sigma_{p_c}(q)^2 < infinity` for every `s >= 0`.

**Dichotomy.** Over a rapid-decay quotient, critical fibre tails either decay
exponentially, or satisfy `b_R(p_c) >= C^(-2) (1+R)^(-2D)` at every radius
`R >= 1`.

**For free quotients.** Haagerup's inequality on spheres makes (b) the explicit
condition `(1+R_0)^2 b_{R_0}(p_c) < 1`. It holds on every generating set, with no
tree-projection hypothesis.

Proof: artifact Theorem 3.1.
