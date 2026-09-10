---
rg: 2
id: fpbs-universal-subcritical-pivotal-growth-rate
kind: claim
title: Every nonamenable Cayley graph admits a near-critical pivotal growth rate below half its spectral gap exponent
---

OPEN. For every fixed nonamenable Cayley graph, does some p0 in (pc,1) satisfy limsup_n log(1+L_n(p0))/n < (-log rho)/2, where L_n(p0)=sup_(R>=n,pc<=p<=p0) E_p[N_(n,R)|E_(n,R)]/n? The supremum may be infinite. No such universal upper bound is established. This is a sufficient target, not an asserted equivalent formulation.

## Attempts

* **Contradict the necessary spike.** `fpbs-collapse-exponential-pivotal-spikes`
  proves that `p_c=p_u=c` forces, for every `alpha<lambda_0/2` and all large
  `n`, a radius `R_n>=n` and a parameter `t_n` in `(c,c+exp(-alpha n))` with
  `E_(t_n)[N_(n,R_n)|E_(n,R_n)] >= [c(lambda_0-2alpha)/2] n exp(alpha n)`,
  hence `liminf_n n^(-1)log(1+L_n(p_0)) >= lambda_0/2`. Any strict upper
  estimate below `lambda_0/2`, in particular any subexponential bound on
  `L_n`, would therefore close `fpbs-benjamini-schramm-universal`. **Where it
  dies:** Section 6 of `research/artifacts/fpbs/spectral-spike.md` states
  plainly that this is not a contradiction. The witnessing radius `R_n` is
  unbounded, `L_n(p_0)` may be `+infinity` as a supremum over `R>=n`, and the
  trivial bound `N_(n,R)<=|E(B_R)|` permits exactly that growth. Uniformity in
  `R` is essential and a bound at one radius does not suffice.
* **Get the upper bound from critical decay.** Theorem 3.1 of the same note
  gives the two-sided finite-cluster estimate
  `(1-theta(p)) r_n <= f_n(p) <= (1-theta(p)) rho^n` and hence
  `lim_n n^(-1) log a_n(c) = log rho`. **Where it dies:** the
  uniqueness-phase decomposition (4.4) isolates a spectral atom of mass
  `theta(p)^2` at `1`, with all remaining mass at or below `rho`. That atom
  can be arbitrarily small and still dominate long-time sampling, so critical
  decay places no upper bound on the near-critical logarithmic derivative.
* **Argue that the exponential scale is impossible.** **Where it dies:**
  Section 7 exhibits a monotone factor-of-iid partition model on the same
  graph whose logarithmic-derivative peak has normalized rate exactly
  `lambda_0/2`, matching the scale of the required spike. The model is not
  bond percolation, its threshold is zero rather than `c>0`, and identifying
  its derivative with a Bernoulli pivotal count is an error the note names
  explicitly. It does show that no argument using only the spectral
  decomposition can exclude the scale.
