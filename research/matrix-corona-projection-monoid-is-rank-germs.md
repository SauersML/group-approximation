---
rg: 2
id: matrix-corona-projection-monoid-is-rank-germs
kind: claim
title: Stable matrix-corona projections are classified and compared by eventual rank germs
artifacts:
  - research/matrix-corona-projection-monoid-is-rank-germs-proof.md
---

For positive integers `d_n`, let

```text
Q_d=(prod_n M_(d_n)(C))/(directSum_n M_(d_n)(C))
```

and let `D_d^+` be the monoid of nonnegative integer sequences `r=(r_n)`
satisfying `r_n<=k d_n` for some fixed `k`, modulo eventual equality.

Every stable projection `p` over `Q_d` has a projection lift `(p_n)`, and

```text
Dim_Q(p)=[rank(p_n)]
```

induces an ordered-monoid isomorphism

```text
V(Q_d) ~= D_d^+.
```

More precisely, for stable projections `p,q`,

```text
p is Murray-von Neumann subequivalent to q
  iff rank(p_n)<=rank(q_n) eventually.
```

Consequently `V(Q_d)` is conical and cancellative, its algebraic order is
literal eventual rank comparison, and `D=2D` forces `D=0`.  A projection has
zero dimension exactly when it is zero.

The Grothendieck completion recovers
`K_0(Q_d)=L(d)/(directSum_n Z)`, so this projection theorem is the positive,
order-sensitive refinement of the existing K-zero computation.
