---
rg: 2
id: hard-soft-threshold-exponent-proof
kind: route
title: Compare Markov hard cost with the optimistic quadratic anchor remainder
target: hard-soft-thresholds-cannot-enter-anchor-contraction
requires:
  - all-dual-unique-neighbors-contract-operator-tails
  - one-anchor-grading-makes-parity-damage-quadratic
  - operator-tail-contraction-misses-uniform-diffuse-matching
---

Equation `(HST2)` is Markov's inequality applied to `(HST1)`.  Since a hard
replacement moves a reflection by at most squared normalized-HS distance
`4`, its average metric cost is a universal multiple of `|U_t|/L`.

Under the generously strengthened low-core hypothesis
`||Y_(a,i)||_infty<=t`, every term with two odd factors is bounded by putting
one odd factor in operator norm and summing the other in `L_2`.  Normalized
Cauchy--Schwarz gives `(HST4)`.  Comparing it to the linear energy `E` gives
`(HST5)`, while `(HST2)` gives `(HST3)`.

Finally `(HST6)` is exactly `(AUT2)`.  The uniform diffuse profile from
`operator-tail-contraction-misses-uniform-diffuse-matching` proves that the
recurrence cannot be initiated below the RMS threshold.  This completes the
no-go for every scalar multiscale schedule based only on these inputs.

