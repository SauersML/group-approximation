---
rg: 2
id: stw99-lxvi-dyadic-stage-ultraproduct-is-not-simple-proof
kind: route
title: A vanishing matrix fraction gives a nonzero nonfull ultraproduct projection
target: stw99-lxvi-dyadic-stage-ultraproduct-is-not-simple
requires: []
---

For each `n`, choose a rank-one projection `e_n` in the unital copy of
`M_(k_n)` and put `e=[(e_n)] in prod_omega A_n`.  Since `||e_n||=1`, the
class `e` is a nonzero projection.

We show that `e` is not full.  If it were full, there would be a natural
number `m` and elements `x_1,...,x_m` in the ultraproduct such that

```text
||sum_i x_i* e x_i-1|| < 1.
```

Represent the `x_i` by bounded sequences.  On an `omega`-large set the same
strict inequality holds in `A_n`.  It implies, by the standard
positive-element comparison lemma,

```text
1_(A_n) Cuntz-below e_n directSum ... directSum e_n       (m copies).
```

For all sufficiently large `n`, the projection on the right is Murray--von
Neumann equivalent to the sum `p_n` of `m` mutually orthogonal rank-one
projections in the displayed `M_(k_n)`, and `p_n<1_(A_n)` because `m<k_n`.
Comparison of projections gives `1_(A_n)` Murray--von Neumann subequivalent
to `p_n`.  Since `p_n<=1_(A_n)`, this would make the finite projection
`1_(A_n)` equivalent to a proper subprojection of itself, a contradiction.

Thus `e` generates a proper nonzero ideal, and the ultraproduct is not
simple.
