---
rg: 2
id: every-high-free-root-valuation-has-a-rank-one-e5-detector-proof
kind: route
title: Shift a dyadic pulse to the first nontrivial monomial
target: every-high-free-root-valuation-has-a-rank-one-e5-detector
requires:
  - dyadic-e5-hard-pulses-have-disjoint-degree-bands
  - e5-heisenberg-word-realizes-rank-one-boundary-pulse
---

For `r>=2`, repeatedly double `n` from one until `(VCD2)` holds.  The dyadic
pulse theorem says that `Delta_n` has degree `4n-2`, with unique leading
coefficient `e_13^*`, and every other coefficient has smaller degree.

Scaling the `p` half of a Heisenberg frame by `x^t` scales all its cross
commutators by `x^t`; the `p` roots still commute with one another.  Doing
this in both source and coefficient copies preserves their level-zero
matching, while the one-sided difference is exactly `(VCD3)`.  Its leading
degree is

```text
t+(4n-2)=r,                                                (VCD4)
```

and scaling cannot create another leading coordinate.  A relative character
of valuation `r` is trivial on every lower monomial and negative on `x^r`.
Entrywise evaluation of `(VCD3)` is therefore `(VCD1)`, whose alternating
matrix has rank two.

It remains only to bound word size.  Every root `e_ij(x^t)` is a word in the
finite root alphabet with coefficients `1,x`.  For an intermediate index
`k` distinct from `i,j`, the Steinberg relation gives

```text
e_ij(x^(a+b))=[e_ik(x^a),e_kj(x^b)].                     (VCD5)
```

Choose `a=floor(t/2)`, `b=ceil(t/2)` recursively.  If `L(t)` denotes the
resulting word length, then

```text
L(t)<=2L(a)+2L(b),    L(0)=L(1)=1,
```

so `L(t)<=4t^2` for `t>=1`.  The transporter power has length `O(n)<=O(r)`.
This proves the claimed quadratic bound.
