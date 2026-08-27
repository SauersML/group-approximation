---
rg: 2
id: outcome-count-free-subpovm-completion-proof
kind: route
title: Add one deficit outcome, orthogonalize simultaneously, and merge it back
target: outcome-count-free-subpovm-completion
requires: []
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
---

Set `a_0=1-s`.  Then `(a_0,a_1,...,a_m)` is an exact POVM and its total
purity deficit is

```text
D=tau(a_0-a_0^2)+sum_j tau(a_j-a_j^2)<=mu+eta.        (SPP1)
```

The constant-nine simultaneous POVM orthogonalization used in Section 4 of
Mančinska--Spaas--Spirig--Vernooij gives a PVM `(r_0,...,r_m)` with

```text
sum_(j=0)^m||a_j-r_j||_2^2<=9D.                       (SPP2)
```

Define `q_1=r_0+r_1` and `q_j=r_j` for `j>=2`.  Orthogonality and positivity
give

```text
||a_1-q_1||_2^2<=||a_1-r_1||_2^2+tau(r_0),
tau(r_0)<=||a_0-r_0||_2^2+2mu.                        (SPP3)
```

When `(SPP3)` is summed with the unchanged errors, the omitted zeroth error
cancels and yields `9(mu+eta)+2mu=11mu+9eta`.  Applying this proof in every
corner `p_kMp_k`, with normalized corner trace and then multiplying back by
`tau(p_k)`, proves the block-preserving form.

