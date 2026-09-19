---
rg: 2
id: sublinear-eigenmap-metric-entropy-implies-uniform-gamma
kind: claim
title: Sublinear eigenmap metric entropy implies uniform property Gamma
distinct_from:
  asymptotically-clustered-diagonal-ah-has-uniform-gamma: that theorem assumes a packet decomposition directly; this gives an intrinsic covering-number condition which produces the packets and is strictly broader than its sublinear-distinct-eigenmap corollary.
  point-dominated-diagonal-ah-has-uniform-gamma: that theorem discards all nonconstant coordinate maps after assuming their total weight vanishes; this criterion permits arbitrary coordinate weight when the eigenmaps have sublinear metric entropy on each finite early-stage test set.
  stw99-problem-xx-villadsen-algebras-uniform-gamma: independently variable multiplicity-one coordinate projections have linear covering number for a separating scalar function, so this theorem does not settle the positive-radius Villadsen case.
artifacts:
  - research/artifacts/stw99-xx-eigenmap-metric-entropy-2026-08-30.md
---

Let

```text
A = lim_n (C(X_n) tensor M_(r_n),phi_n)
```

be a unital simple diagonal AH algebra, and write a later composite using
its eigenmap multiset

```text
Lambda_(n,m)={lambda_1,...,lambda_L},
L=L_(n,m)=r_m/r_n.
```

For a finite subset `F` of the unit ball of the `n`th building block, put

```text
d_F(lambda,mu)
 = sup_(y in X_m) max_(a in F)
      ||a(lambda(y))-a(mu(y))||.
```

This is a pseudometric on the eigenmap multiset.  Let
`N_(n,m)(F,delta)` be the least number of `d_F`-balls of radius `delta`
needed to cover that multiset, with multiplicities covered by the same ball.

Assume that for every `n` and finite `F` there are an increasing cofinal
sequence `m_j>n` and numbers `delta_j>0` such that

```text
delta_j -> 0,
N_(n,m_j)(F,delta_j)/L_(n,m_j) -> 0.                 (ME1)
```

Then `A` has uniform property Gamma.

Condition `(ME1)` is strictly weaker than sublinear distinct-eigenmap count.
Indeed `N_(n,m)(F,delta)` is at most the number of distinct eigenmaps, but
`L` distinct eigenmaps may still lie in `o(L)` shrinking `d_F`-balls.  For
example, a multiset of `L_j` distinct maps covered by `sqrt(L_j)` balls of
radius `delta_j->0` satisfies `(ME1)` while its distinct-map ratio is one.
