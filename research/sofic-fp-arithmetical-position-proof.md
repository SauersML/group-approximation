---
rg: 2
id: sofic-fp-arithmetical-position-proof
kind: route
title: Adian--Rabin lower bound from the nonsofic seed plus the permutation upper bound
target: sofic-recognition-finite-presentations-arithmetical-position
requires:
  - sofic-recognition-has-a-pi2-upper-bound
  - finitely-presented-nonsofic-group-exists
  - second-level-rice-theorem-for-local-approximation-properties
---

Clause (a) of [[second-level-rice-theorem-for-local-approximation-properties]]
for `P` = sofic, with (H1) residually finite groups sofic and (H2) the
finitely presented nonsofic group of
[[finitely-presented-nonsofic-group-exists]], gives `Sigma^0_1`-hardness of
`SOFIC_fp` and `Pi^0_1`-hardness of `NONSOFIC_fp`; the sofic instance of the
Markov argument is machine-checked in `Computability/SoficMarkov`.
Membership is [[sofic-recognition-has-a-pi2-upper-bound]] restricted to
finite presentation codes.  A `Sigma^0_1`-hard set is not `Pi^0_1` and a
`Pi^0_1`-hard set is not `Sigma^0_1`.
