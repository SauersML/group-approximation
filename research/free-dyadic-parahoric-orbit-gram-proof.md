---
rg: 2
id: free-dyadic-parahoric-orbit-gram-proof
kind: route
title: Orbit one diffuse free-lamp projection over the index-forty-two parahoric
target: free-dyadic-parahoric-orbit-has-41-over-42-gram-floor
requires:
  - free-hnn-outlier-has-dyadic-a2-pvm-tower
  - native-sl3-edge-parahoric-has-index-forty-two
---

The second prerequisite gives `[C:D]=42`.  If `g_iD!=g_jD`, then
`g_i hC!=g_j hC`: equality would imply
`g_j^(-1)g_i in C cap hCh^(-1)=D`.  Thus the forty-two algebras
`D_(g_i hC)` are distinct members of the free family in `(DPT3)--(DPT4)`.

The stabilizer `D` fixes `hC`.  Exact covariance consequently fixes its
lamp generator and its whole spectral algebra pointwise, so `(FDO3)` is
independent of representatives.  Center `E` as `E=pI+E_0`.  For `i!=j`,
freeness of the two distinct lamp algebras gives

```text
tau(E_iE_j)=tau(E_i)tau(E_j)=p^2,
```

which proves `(FDO4)`.

For completeness, two free projections of traces `alpha,beta` are in
general position: their meet has trace

```text
max(alpha+beta-1,0).
```

This is the free-projection meet formula (equivalently, the mass at `1` in
the spectral distribution of `E_iE_jE_i`).  Taking
`alpha=beta=p<=1/2` proves `(FDO5)`.

At `p=1/42`, expansion and `(FDO4)` give

```text
||sum_i E_i-I||_2^2
 =sum_i tau(E_i)+sum_(i!=j)tau(E_iE_j)
   -2sum_i tau(E_i)+1
 =1+41/42-2+1
 =41/42.
```

The diffuse algebra `D_(hC)` contains a projection of every prescribed
trace in `[0,1]`, so this calculation uses the entire all-depth completion,
not merely a fixed dyadic level.  Weyl conjugation repeats the identical
argument for the other five index-forty-two parahorics.
