---
rg: 2
id: weighted-median-coarea-relative-cut
kind: claim
title: Weighted spectral coarea gives a small-side relative cut from every low-energy witness
---

Let `(M_d,tau)` carry normalized trace, let `a_1,...,a_m` be contractions, and
let `x=x^*` satisfy

```text
tau(x)=0,
||x||_2=1,
E=sum_(s=1)^m ||a_s x-x a_s||_2^2.
```

Then there is a nonzero projection `q` with `tau(q)<=1/2` such that

```text
sum_s ||a_s q-q a_s||_2^2
  <= 2 sqrt(2 m E) tau(q).                            (WMC)
```

No bound on `||x||_infinity` is assumed and the `a_s` need not be unitaries or
normal.  Thus the spiky regime does not obstruct extraction of a
**relative-boundary** cut; spikes only force the selected side to have small
trace.
