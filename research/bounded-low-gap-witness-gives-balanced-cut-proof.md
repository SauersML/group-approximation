---
rg: 2
id: bounded-low-gap-witness-gives-balanced-cut-proof
kind: route
title: Mean-zero variance forces two tails, then spectral coarea chooses the cut
target: bounded-low-gap-witness-gives-balanced-cut
requires: []
---

Write `x=x_+-x_-` with `x_+ x_-=0`, and let

```text
mu=tau(x_+)=tau(x_-),
```

where equality follows from `tau(x)=0`.  Since `0<=x_+,x_-<=C`,

```text
1=tau(x^2)=tau(x_+^2)+tau(x_-^2) <= 2 C mu,
```

so `mu>=1/(2C)`.

Set `a=1/(4C)`.  If

```text
r_+ = tau(1_[a,infinity)(x)),
```

then the positive first moment is bounded by

```text
mu=tau(x_+) <= a + C r_+.
```

Hence `r_+ >= (mu-a)/C >= 1/(4C^2)`.  Applying the same argument to
`-x` gives

```text
tau(1_(-infinity,-a](x)) >= 1/(4C^2).
```

Therefore every spectral cut `q_t=1_[t,infinity)(x)` with `t in [-a,a]`
satisfies

```text
1/(4C^2) <= tau(q_t) <= 1-1/(4C^2).
```

Now put `H=(x+C)/(2C)`, so `0<=H<=1`.  The interval `t in[-a,a]` becomes an
interval of `H`-thresholds of length

```text
(2a)/(2C)=1/(4C^2).
```

Apply the common-threshold spectral coarea estimate `(SCI5)` from
`TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md` to the unitaries `u_s`.  Since

```text
||[H,u_s]||_2 = (1/(2C)) ||[x,u_s]||_2,
```

there is one threshold in that interval such that

```text
sum_s ||[q,u_s]||_2^2
 <= 4C^2 * (1/(2C)) * sum_s ||[x,u_s]||_2
 = 2C sum_s ||[x,u_s]||_2
 <= 2C sqrt(m E),
```

where the last step is Cauchy--Schwarz over the finite generator set.  The
trace balance was proved uniformly for every threshold in the interval, so
it holds for this coarea-selected `q` as well.
