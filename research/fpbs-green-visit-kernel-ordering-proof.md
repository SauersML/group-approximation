---
rg: 2
id: fpbs-green-visit-kernel-ordering-proof
kind: route
title: Sum finite-volume Russo over walk lengths and pair the connectivity with the l2 Green function
target: fpbs-green-visit-kernel-ordering
requires:
  - fpbs-critical-walk-correlation
artifacts:
  - research/artifacts/fpbs/docs/green-visit-kernel-2026-09-17.md
---

Complete proofs are in Sections 1–3 of the artifact. No computation is used.

1. **Walk sums.** Since `sum_n P(Bin(n,1/2)=k)=2`, we get `A_L=2A_S`. The
   critical bound `a^S_n(c)<=rho_S^n` is the required node. Binomial averaging
   gives `a^L_n(c)<=rho_L^n`. So `A(c)<=1/(1-rho)` for both walks. Also
   `||g||_2 <= sum_n mu^(2n)(e)^(1/2) <= 1/(1-rho)`.
2. **(b)** Integrate `d/dp log A_R = E^tilt/p`, then let `R->infinity` by
   monotone convergence.
3. **(c)** PB integrates to `a_(n,R)(p) <= r^n`, with
   `r=rho_L(p1/c)^C<1` on a shorter interval `[c,p1]`. The numerator is then
   at most `C r/(1-r)^2`, and `A_R>=a_(0,R)=1`.
4. **(d)** The BK bubble (step 1 of
   `fpbs-l2-gap-gives-bounded-pivotal-counts-proof`) gives
   `E[N_(n,R);E_(n,R)] <= p W_n`. Summing over `n` gives
   `sum_n W_n <= <g, tau*A*tau> <= ||g||_2 d ||T_p||^2`. This uses symmetry of
   `tau` for the left-convolution norm, and monotonicity of `||T_p||` in `p`.
5. **(e)** By finite Russo, `B(eps)=lim_n n^(-1) log(a_n(c+eps)/a_n(c))`.
   With `a^L_n(c)<=rho_L^n`, NC forces exponential decay of `a^L_n(c+eps)`.
6. **(f)** `A=<g,tau_p>`. Apply Cauchy–Schwarz.
