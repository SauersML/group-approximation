---
rg: 2
id: stw82-spectral-support-hall-capacity-proof
kind: route
title: Extend coverage to range projections and charge each spectral cut to its available labels
target: stw82-spectral-support-hall-capacity
requires: []
---

Put `a_v=1-sum_k c_(v,k)`.  Equation (H1) says `a_v h_v=0`.
The range of `h_v` is dense in `p_v H` in any faithful normal
representation of `M`, so boundedness gives

```text
a_v p_v=0.
```

Consequently

```text
p_v=sum_k c_(v,k)p_v.
```

After taking the trace and compressing cyclically,

```text
tau(p_v)
 =sum_(k in L_v) tau(p_v c_(v,k) p_v)
 <=sum_(k in L_v) tau(c_(v,k)).                      (P1)
```

For fixed `k`, (H2) makes the cutters indexed by `v` pairwise
orthogonal.  Their sum is a positive contraction.  Hence, for any
`S subseteq V`, summing (P1) and reversing the order of summation gives

```text
sum_(v in S) tau(p_v)
 <=sum_(k in union_(v in S)L_v)
      sum_(v in S) tau(c_(v,k))
 <=|union_(v in S)L_v|.
```

If `c_(v,k)<=q_k`, orthogonality makes the fixed-`k` sum at most `q_k`,
which proves (H4).

For the approximate assertion, let `p=p_(v,lambda)`.  Functional calculus
gives `b in pMp` with

```text
h_v b=p,                 norm(b)<=1/lambda.
```

Thus

```text
norm(a_v p)=norm(a_v h_v b)<=eta/lambda.             (P2)
```

Compressing (P2), taking the trace, and using (P1)'s inequality gives

```text
(1-eta/lambda)tau(p)
 <=sum_(k in L_v) tau(c_(v,k)).                      (P3)
```

Summing (P3) over `S` proves (H5) and its capacity-projection variant.

For the scalar witness, (H2) says one of `c_(I,1),c_(Q,1)` is zero.  The
corresponding error is

```text
norm((1-0)(1/2))=1/2.
```

This also proves the claimed quantitative floor.

