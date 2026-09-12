---
rg: 2
id: fpbs-sphere-cut-fibre-tails-proof
kind: route
title: Cross the fibre-saturated sphere, apply BK, bound the convolution by its operator norm, and iterate
target: fpbs-sphere-cut-fibre-tails-decay-exponentially
requires: []
artifacts:
  - research/artifacts/fpbs/docs/sphere-cut-fibre-bootstrap.md
---

1. **Sphere cut.** Along an edge of `Cay(Gamma,S)` the quotient length changes by
   at most one. A path from `o` to `Gamma_q` with `|q| >= R` meets
   `pi^(-1)(S_Q(R))`.
2. **BK at the first crossing.** The two segments of a simple open path are
   edge-disjoint. The van den Berg–Kesten inequality and transitivity give
   `sigma_p(q) <= sum_{|q'|=R} sigma_p(q') sigma_p(q'^(-1) q)` with
   `|q'^(-1) q| >= |q| - R`.
3. **Operator norm.** For `p < p_c`, `sigma_p` lies in `l1(Q)` by sharpness.
   Squaring the pointwise bound over `|q| >= R + m` gives
   `T_{R+m} <= ||lambda(sigma_{p,R})||^2 T_m`.
4. **Iteration and uniformity.** The norm is monotone in `p`, so at radius `R_0`
   it is at most `theta < 1` for all `p < p_c`. Iterating gives
   `T_m(p) <= theta^(floor(m/R_0)) B_p`.
   * `B_p` is bounded by `(1-theta)^(-1)` times the finitely many small-sphere
     terms.
   * Harris–FKG makes each of those at most `p^(-2L) b_{R_0}(p) <= p^(-2L) theta`.
5. **Limit.** Left-continuity and monotone convergence carry the bound to `p_c`.
   Summation by parts gives every polynomially weighted bubble.

Full proof: artifact Theorem 2.1.
