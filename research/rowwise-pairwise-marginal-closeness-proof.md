---
rg: 2
id: rowwise-pairwise-marginal-closeness-proof
kind: route
title: Intersect two row masks and compute the free-product distance
target: rowwise-shared-involution-forces-pairwise-marginal-closeness
requires: []
---

Let `p=q_i meet q_j` in `M`.  The codimension inequality gives

```text
tau(1-p)<=tau(1-q_i)+tau(1-q_j).                       (PIC5)
```

Both equalities in `(PIC1)` hold on `p`, so `(A_i-A_j)p=0`.  Since
`T=(A_i-A_j)/2` is a contraction,

```text
(1/4)||A_i-A_j||_2^2=||T(1-p)||_2^2
 <=tau(1-p),                                           (PIC6)
```

which proves `(PIC2)`.

For distinct free factors, write `A_k=m_k 1+A_k^0`.  The centered alternating
moment vanishes, hence `tau(A_iA_j)=m_i m_j`.  Self-adjoint unitarity gives

```text
||A_i-A_j||_2^2
=tau((A_i-A_j)^2)=2-2m_i m_j.                          (PIC7)
```

Divide by four and combine with `(PIC2)`.

For the Fourier specialization, both mask deficits are `1/p`, so `(PIC2)`
and `(PIC7)` give

```text
2-2 alpha gamma=||A_(c,x)-A_(d,x)||_2^2<=16/p,
```

which is `(PIC9)`.  Since `|alpha|,|gamma|<=1` and `1-8/p>0`, the traces
have the same sign and each absolute value is at least `1-8/p`.  For
`s_x=sgn(alpha)=sgn(gamma)`, involutivity gives

```text
||A_(c,x)-s_x I||_2^2=2-2|tau(A_(c,x))|<=16/p,        (1)
```

proving `(PIC10)`.  The spectral distribution of `A_(c,x)` under the
context PVM satisfies

```text
nu_c(a_x!=s_x)=(1-s_x tau(A_(c,x)))/2<=4/p.           (2)
```

The union bound proves `(PIC11)`.  If `s|_(U_c)` were forbidden, its atom
would contribute at least `1-4|U_c|/p` to the forbidden mass.  Under
`(PIC12)` this is strictly larger than `1/p`, contradicting the Fourier
predicate-mask construction.  Hence every rounded context tuple is allowed,
and the common signs satisfy the whole BCS.
