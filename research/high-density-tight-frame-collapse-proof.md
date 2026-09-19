---
rg: 2
id: high-density-tight-frame-collapse-proof
kind: route
title: The deleted mask pieces must cover every nontrivial tight carrier
target: high-density-tight-defect-frame-collapses-to-common-carrier
requires:
  - tight-defect-cubic-is-weighted-fusion-frame
---

Let `W=sum_i w_i` and write the tight fusion-frame identity as

```text
sum_i w_i r_i=mu p.                                    (HDFP1)
```

Subtracting from `Wp` and using `l_i=p-r_i` gives

```text
sum_i w_i l_i=(W-mu)p.                                 (HDFP2)
```

If `W=mu`, positivity and `w_i>0` force every `l_i=0`; hence every
`r_i=p`.  If `W!=mu`, the left side of `(HDFP2)` has support `p`.  Therefore

```text
p=join_i l_i,
tau(p)<=sum_i tau(l_i)<=sum_i tau(1-q_i),              (HDFP3)
```

which proves `(HDF4)`.

To justify `(HDF1)`, the canonical support projection `p` is the range
projection of `D_wD_w^*`.  The projection-CRT calculation in
`shared-involution-right-ideal-interpolation-criterion` gives
`pq_i=e_iq_i=r_i`.  Since `pq_i` is a projection, the compression lemma
there also gives `q_ip=pq_i`; this proves `(HDF1)--(HDF3)`.

Finally `r_i=e_iq_i` and `[e_i,q_i]=0`, so

```text
tau(r_i)>=tau(e_i)-tau(1-q_i).
```

As `r_i<=p`, this proves `(HDF7)--(HDF8)`.  With equal deficits `1/P`,
`r/P<1/2-1/P` is equivalent to `P>2(r+1)`, giving `(HDF9)`.
