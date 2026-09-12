---
rg: 2
id: agent-stw77-zero-near-witnesses-descend-properness
kind: claim
title: Operator-norm-near corner witnesses descend proper infiniteness
distinct_from:
  agent-stw77-zero-type-i-properness-does-not-descend: that shows exact descent of the support projection alone is insufficient; this identifies the additional quantitative datum that does suffice.
  stw77-fd-commutant-splitting-iff-proper-supports: that starts with proper infiniteness inside the C-star target; this transfers it from a represented type-I target when the witnesses themselves are norm-near the C-star target.
---

Let `pi:B->B(H)` be a faithful representation, let `p in B` be a
projection, and put `q=pi(p)`.  Suppose there are `w_1,w_2 in qB(H)q` with

```text
w_i^*w_j=delta_(i,j)q
```

and

```text
max_i dist(w_i,pi(B))<1/4.
```

Then `p` is properly infinite in `B`.

Consequently, after a finite-dimensional absorbed model has been perturbed
into `pi(B)`, it is enough to descend the two type-I corner isometries for
each minimal support within the universal norm tolerance `1/4`.  No
Kadison--Kastler control of an infinite generated algebra is needed.

This is the precise extra datum missing in
`agent-stw77-zero-type-i-properness-does-not-descend`: in the infinitely
amplified Toeplitz--Cuntz defect, every pair splitting `pi(e)` stays at least
`1/4` from `pi(T_2)`.
