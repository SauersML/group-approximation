---
rg: 2
id: weighted-median-coarea-relative-cut-proof
kind: route
title: Center at a median and integrate spectral boundary against 2t
target: weighted-median-coarea-relative-cut
requires: []
---

Choose a median `mu` of the finite spectral distribution of `x`, so both
strict sides have trace at most `1/2`.  Put

```text
y_+=(x-mu)_+,
y_-=(mu-x)_+.
```

Their supports are the two strict median sides.  Since `tau(x)=0`,

```text
||x-mu||_2^2=||x||_2^2+mu^2>=1,
||x-mu||_2^2=||y_+||_2^2+||y_-||_2^2.
```

Choose `y` among `y_+,y_-` with `||y||_2^2>=1/2`; its support has trace at
most `1/2`.

For every contraction `a`, positive-part functional calculus contracts the
Hilbert--Schmidt commutator:

```text
||[a,y]||_2 <= ||[a,x]||_2.
```

This is entrywise in an eigenbasis of `x`: the scalar maps
`t |-> (t-mu)_+` and `t |-> (mu-t)_+` are 1-Lipschitz.

For `t>0` let `P_t=1_[t,infinity)(y)`.  In an eigenbasis of `y`, with
eigenvalues `lambda_i>=0`, weighted coarea gives

```text
integral_0^infinity 2t ||[P_t,a]||_2^2 dt
 = (1/d) sum_(i,j) |lambda_i^2-lambda_j^2| |a_ij|^2.
```

Factor
`|lambda_i^2-lambda_j^2|=|lambda_i-lambda_j|(lambda_i+lambda_j)` and apply
Cauchy--Schwarz.  The two factors are `||[y,a]||_2` and
`||ya+ay||_2`, and the latter is at most `2||y||_2` because `||a||_op<=1`.
Hence

```text
integral 2t ||[P_t,a]||_2^2 dt
 <= 2 ||y||_2 ||[y,a]||_2.
```

Summing over `s` and using Cauchy--Schwarz once more,

```text
integral 2t sum_s ||[P_t,a_s]||_2^2 dt
 <= 2 ||y||_2 sqrt(m E).
```

On the other hand layer cake gives

```text
integral_0^infinity 2t tau(P_t) dt = tau(y^2)=||y||_2^2.
```

Therefore some `t>0` with `P_t!=0` satisfies

```text
sum_s ||[P_t,a_s]||_2^2 / tau(P_t)
 <= 2 sqrt(mE)/||y||_2
 <= 2 sqrt(2mE).
```

Take `q=P_t`.  Since `q` lies under the strict median-side support,
`tau(q)<=1/2`.  This proves `(WMC)`.
