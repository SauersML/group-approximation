---
rg: 2
id: dyadic-e5-hard-pulses-have-disjoint-degree-bands
kind: claim
title: Dyadic hard-pulse iterates occupy pairwise disjoint free-root degree bands
artifacts:
  - experiments/e5_heisenberg_rank_one_boundary_pulse.py
distinct_from:
  e5-heisenberg-word-realizes-rank-one-boundary-pulse: that identifies one unique leading coefficient at every iterate; this passes to dyadic iterates and proves every coefficient, not just the leader, lies in a band disjoint from all other selected iterates.
  free-root-top-boundary-reservoir-is-summable: that proves an abstract trace budget for first-detection layers; this supplies explicit pairwise-disjoint polynomial degree intervals to which a band version of that budget can be applied.
---

Use the notation of the `E_5(F_2[x])` Heisenberg pulse.  If `n=2^k`, then

```text
c_n=x^(2n-1),
d_n=1+sum_(j=1)^k x^(2n-2^j),                            (DHP1)
```

where `S^n=[[a_n,c_n],[c_n,d_n]]`.  The relative hard pulse is

```text
Delta_n=(d_n^2+1)e_02^*+c_nd_n(e_03^*+e_12^*)
          +c_n^2e_13^*.                                  (DHP2)
```

Every monomial appearing in `Delta_n` therefore has degree in

```text
B_k=[2n-1,4n-2]=[2^(k+1)-1,2^(k+2)-2].                   (DHP3)
```

The bands `B_0,B_1,...` are consecutive and pairwise disjoint.  Moreover the
left endpoint occurs in the two mixed coordinates and the right endpoint is
the unique term `x^(4n-2)e_13^*`.

Thus the one-sided clock admits a sparse subsequence with no lower-degree
tails leaking into earlier reservoirs.  This does not by itself make the
spectral carrier projections orthogonal—a character may be nontrivial on
several bands—but it removes polynomial overlap from the remaining
persistence/first-hit argument.
