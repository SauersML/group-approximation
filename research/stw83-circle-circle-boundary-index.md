---
rg: 2
id: stw83-circle-circle-boundary-index
kind: claim
title: Every genuine finite circle-by-circle graph extension has a nonzero positive path index
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `F` be a finite graph with

```text
F^0 = V_0 disjoint_union V_1 disjoint_union V_2
```

and the following properties.

1. The induced graphs on `V_0` and `V_2` are simple directed cycles.
2. The induced graph on `V_1` is acyclic, and every vertex of `V_1` reaches
   `V_2`.
3. There is no edge from `V_i` to `V_j` when `i>j`.
4. At least one edge leaves `V_0` for `V_1 union V_2`.

Put `H=V_1 union V_2` and `I=I_H`.  Then `H` is saturated hereditary,
`I` is Morita equivalent to `C(T)`, and

```text
C*(F)/I = M_|V_0|(C(T)).                               (1)
```

Define integers `n(v)` backwards through the acyclic connector by

```text
n(v)=1                                      for v in V_2,
n(v)=sum_{e: s(e)=v} n(r(e))                for v in V_1,
```

and set

```text
N=sum_{e: s(e) in V_0, r(e) in H} n(r(e)).              (2)
```

Give `K_1(M_|V_0|(C(T)))=Z` the generator determined by the oriented upstream
cycle and give `K_0(I)=Z` the generator represented by any downstream cycle
vertex.  With the boundary convention

```text
partial_1([u])=[P-x*x]-[P-xx*]
```

for a partial-isometry lift `x` of a quotient unitary `u`, one has

```text
partial_1: Z -> Z,             partial_1(1)=-N.         (3)
```

Changing the generator or boundary-sign convention changes `-N` to `N`; the
intrinsic conclusion is `|partial_1(1)|=N>=1`.  Thus every genuine extension
in this class is nonsplit and admits no quasicentral approximate unit of
projections for `I`.  The upstream cycle projection is infinite.  Neither a
splitting argument nor quasidiagonal-extension color reuse can therefore
resolve this finite circle-ideal/circle-quotient frontier.  The estimate
`dim_nuc(C*(F))<=1` remains open.
