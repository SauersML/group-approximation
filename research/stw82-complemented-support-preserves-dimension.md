---
rg: 2
id: stw82-complemented-support-preserves-dimension
kind: claim
title: Complemented central support makes multiplier-projection adjunction dimension-neutral
distinct_from:
  stw82-split-af-is-one-multiplier-projection-problem: that theorem proves the formula when the multiplier projection is full in the whole ideal algebra; the present theorem permits a proper generated ideal, provided that ideal is complemented, and the projection itself need not be central.
  stw82-af-split-stage-centres-obey-maximum: that theorem uses central lifted block units throughout a finite-dimensional quotient exhaustion; the present result treats one arbitrary noncentral multiplier projection by splitting only its generated ideal's central support.
artifacts:
  - research/artifacts/stw82-complemented-multiplier-support-audit-2026-08-30.md
---

Let `A` be a sigma-unital C*-algebra, let `p` be a projection in `M(A)`,
and set

```text
L=closure(ApA).
```

Suppose that `L` is complemented as an ideal of `A`; thus

```text
A=L direct_sum B                                             (CS1)
```

for an ideal `B`.  Equivalently, the support of `L` is represented by a
central projection `z in Z(M(A))`, so that `L=zA` and `B=(1-z)A`.  Then

```text
dim_nuc(A+C p)=dim_nuc(A).                                  (CS2)
```

This genuinely extends both easy extremes of the multiplier-projection
problem.  The projection need not be full in `A`, since `B` may be nonzero,
and it need not be central.  For example, with `H` separable and
infinite-dimensional, take

```text
A=(K(H) tensor M_2) direct_sum C_0((0,1)),
p=(1_(B(H)) tensor e_11,0).
```

Then `p` is neither full nor central in `M(A)`, while its generated ideal is
the complemented first summand, so `(CS2)` applies.

The mechanism is exact.  The definition of `L` forces `p` to annihilate the
complementary ideal `B`; on `L`, the same projection is full.  Consequently

```text
A+C p=(L+C p) direct_sum B,                                 (CS3)
```

the first summand has nuclear dimension `dim_nuc(L)` by the full-support
corner argument, and finite direct sums take the maximum.  Thus the
remaining nonfull frontier is narrower than merely "proper generated
ideal": a counterexample must have generated ideal whose support is not a
central multiplier projection.
