---
rg: 2
id: fpbs-l2-gap-gives-bounded-pivotal-counts-proof
kind: route
title: Bound pivotals by a BK bubble and split the walk around the connectivity operator
target: fpbs-l2-gap-gives-bounded-pivotal-counts
requires: []
artifacts:
  - research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md
---

Complete written proof in Section 4 of the artifact. No computation is used.

1. **BK bubble.** Fix the endpoint `x=X_n`. Every open path from `e` to `x`
   in `B_R` passes through an open pivotal edge `f`. A simple such path
   crosses `f` once, from `u` to `us` say, and its two pieces are disjoint
   witnesses. The BK inequality and monotonicity in the volume give
   `P_p(f open and pivotal) <= p sum over orientations of tau_p(u) tau_p((us)^(-1)x)`.
   Summing over edges and averaging over the walk gives

       E_p[N_(n,R); E_(n,R)] <= p W_n,
       W_n = sum_x mu^n(x) (tau_p*A*tau_p)(x),   A = 1_S.

2. **Split the walk.** Evaluation of a convolution at `e` is cyclic on a
   group, and `mu^j`, `tau_p` and `A` are symmetric. So for `m+m'=n`,

       W_n = < mu^(m')*tau_p , mu^m*tau_p*A >.

   By Cauchy–Schwarz and `||mu^j||_2^2 = mu^(2j)(e)`,

       W_n <= d ||T_p||^2 (mu^(2m)(e) mu^(2m')(e))^(1/2).

3. **Divide by the connection probability.** Since `a_(n,R) >= mu^n(e)`:
   * *Lazy walk.* The return probabilities are nonincreasing, because the
     spectrum lies in `[0,1]`, and satisfy `mu^j(e) >= mu^(j-1)(e)/2`. This
     gives `E[N|E] <= sqrt(2) p d ||T_p||^2`.
   * *Simple walk, odd `n`.* Use instead `a_(n,R) >= p d mu^(n+1)(e)` and
     `mu^(n-1)(e) <= d mu^(n+1)(e)`. This gives
     `E[N|E] <= max(pd, sqrt d) ||T_p||^2`.

   Both bounds are at most `2d||T_p||^2`.
