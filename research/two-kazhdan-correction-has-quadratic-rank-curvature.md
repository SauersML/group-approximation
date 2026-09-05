---
rg: 2
id: two-kazhdan-correction-has-quadratic-rank-curvature
kind: claim
title: Hilbert H2 vanishing leaves arbitrarily small HS curvature outside quadratic-rank supports
artifacts:
  - research/artifacts/flexible-relator-dilation-audit-2026-09-05.md
  - research/artifacts/tapered-curvature-halo-audit-2026-09-05.md
distinct_from:
  two-kazhdan-correction-concentrates-normalized-hs-curvature: that gives trace-norm improvement and supports of vanishing relative rank; this removes all small-angle tangent curvature and gives a quadratic-rank bound for each fixed residual reduction factor.
  orthogonal-frozen-support-surgery-has-square-root-rank-cost: that requires exact reducing supports and a summable repair schedule; these spectral supports need not be invariant and no repair schedule is supplied.
---

Let `G=<S|R>` be finitely presented and assume ordinary
`H^2(G,H_pi)=0` for every unitary Hilbert representation. All matrix
traces and Schatten norms below are normalized. Suppose unitary tuples
`U_j:S->U(d_j)` have positive defining defect

```text
delta_j=max_(r in R)||U_j(r)-I||_2 -> 0.
```

There is a subsequence and tuples `V_j` in the same dimensions with

```text
max_s ||V_j(s)-U_j(s)||_2 = O(delta_j),
max_r ||V_j(r)-I||_2 = O(delta_j).                      (QRC1)
```

Write `E_(j,r)=V_j(r)-I`. The corrected errors satisfy

```text
lim_(t downarrow 0) limsup_j max_r
 ||(E_(j,r)/delta_j) 1_(|E_(j,r)|<=t)||_2 = 0.         (QRC2)
```

Consequently, for every fixed `epsilon>0`, there are projections
`P_(j,epsilon)` and a finite constant `C_epsilon` such that eventually

```text
tr(P_(j,epsilon)) <= C_epsilon delta_j^2,
max_r (||E_(j,r)(I-P_(j,epsilon))||_2
       +||(I-P_(j,epsilon))E_(j,r)||_2)
 <= epsilon delta_j.                                  (QRC3)
```

The same corrected tuples work for every epsilon; the projections and
constant may depend on epsilon and the chosen input subsequence. This is
not an `o(delta_j)` residual with one fixed quadratic-rank constant.
The supports need not commute with the generators. Cutting them out can
therefore create new relator errors and does not yet give stability.

There is a stronger conclusion for inputs whose error energy already
occurs at angles tending to zero:

```text
for every t>0,
 lim_j max_r ||((U_j(r)-I)/delta_j)
                  1_(|U_j(r)-I|>t)||_2 = 0.           (QRC4)
```

Under `(QRC4)`, the output in `(QRC1)` can have HS defining defect
`o(delta_j)` itself. Both uniformly integrable delta-rescaled input
errors and the condition `max_r||U_j(r)-I||_op->0` imply `(QRC4)`.
In the latter case the generator correction also tends to zero in
operator norm, so operator-small defining errors persist after this
one step. No infinite iteration or uniform same-dimension correction
theorem is claimed.

For a fixed reduction factor there is also a uniform finite-scale form.
For every fixed `epsilon>0`, constants `A,C,delta_0>0` depending only
on this presentation and epsilon can be chosen such that every tuple in
every dimension with `0<delta<delta_0` admits `V,P` satisfying

```text
max_s ||V(s)-U(s)||_2 <= A delta,
max_r ||V(r)-I||_2 <= A delta,
tr(P) <= C delta^2,
max_r (||(V(r)-I)(I-P)||_2+||(I-P)(V(r)-I)||_2)
 <= epsilon delta.                                    (QRC5)
```

This fixes epsilon before choosing the constants and makes no assertion
that the constants remain bounded as epsilon decreases.

DERIVATION
small-angle-cohomology-and-hard-curvature-proof
