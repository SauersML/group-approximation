---
rg: 2
id: fpbs-global-pivotal-tail-at-uniqueness
kind: claim
title: Global connection pivotals have uniform endpoint tails at each fixed uniqueness parameter
distinct_from:
  fpbs-uniqueness-pivotals-are-dangling-bridges: that is a deterministic identification of infinite-cluster bridges; this proves uniform quantitative moments and exponential tails by finite-energy surgery and finite-cluster tails.
artifacts:
  - research/artifacts/fpbs/docs/global-pivotal-tails-and-volume-defect.md
---

For Bernoulli bond percolation on a connected nonamenable transitive
graph of degree d, fix p in (p_c,1) with a unique infinite cluster a.s.
Let Z(v,w) count global open connection pivotals, set to zero when
v and w are disconnected, and put chi_f=E_p[|C_o|; |C_o|<infinity].
Then, uniformly in v,w,

    E_p Z(v,w) <= (1+2dp/(1-p)) chi_f.

There are A_p<infinity and b_p>0 such that
P_p(Z(v,w)>=m)<=A_p exp(-b_p m) for every m>=1 and every pair v,w.
The same tail bound conditional on connection holds after multiplying
A_p by theta(p)^(-2). These statements also hold for independent
random endpoints. No uniformity as p decreases to p_c is asserted.

This strengthens the dangling-bridge input used in attempts on
`fpbs-universal-subcritical-pivotal-growth-rate`. Its application to
finite-volume pivotals is governed by `fpbs-pivotal-volume-defect-criterion`.
