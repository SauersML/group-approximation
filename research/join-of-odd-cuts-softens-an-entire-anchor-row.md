---
rg: 2
id: join-of-odd-cuts-softens-an-entire-anchor-row
kind: claim
title: The join of odd spectral cuts softens an entire anchor row at once
distinct_from:
  odd-spectral-anchor-resets-have-monotone-sign-budget: that treats one spectral cut and proves half-sign balance; this joins all site cuts, where half-sign balance need not survive but negative mass remains the exact budget.
  spectral-cut-anchor-reset-pays-boundary-in-one-row: that resets one cut and leaves a coverage question; this covers every high odd site for the anchor in one operation.
  central-adaptive-peeling-or-noncentral-stopping: that must charge the join boundary and averaged negative mass; this removes the number-of-sites scheduling problem.
---

ESTABLISHED.  Fix an anchor reflection `A` and reflections `B_1,...,B_L`.
Put

```text
 R_i=((B_i-AB_iA)/2)^2,
 p_i=1_[s,1](R_i),       p=join_i p_i,       q=1-p.     (JOC1)
```

Every `R_i,p_i` commutes with `A`; hence so do `p,q`.  Since `q<=1-p_i`
and `p_i` is a spectral projection of `R_i`,

```text
 qR_iq<=s q                    for every i.              (JOC2)
```

Reset the anchor by `A'=p+qA`, and write `e_-=(1-A)/2`.  Then

```text
 e_-'=qe_-,
 ||A-A'||_2^2=4tau(pe_-).                               (JOC3)
```

The join need not have balanced anchor signs, so its cost is correctly
expressed as deleted negative mass.  Across repeated join resets for the
current anchor,

```text
 sum_n tau(p_ne_(n,-))<=tau(e_(0,-)),                   (JOC4)
```

even when successive joins overlap.

For the balanced tuple the averaged generator movement is
`4tau(pe_-)/L`.  The row estimate `(SAR4)` applies unchanged: the retained
`q-q` row is operator-soft by `(JOC2)`, and all leakage lies in

```text
 D(p)=(1/L)sum_i||[p,B_i]||_2^2.                        (JOC5)
```

Thus coverage is complete in one join per anchor.  The remaining target is
a join-boundary inequality charging `D(p)/L` and the averaged deleted
negative mass to balanced energy.  Individual coarea bounds do not control
the boundary of a join of noncommuting cuts.
