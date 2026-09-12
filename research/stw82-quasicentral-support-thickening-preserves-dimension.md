---
rg: 2
id: stw82-quasicentral-support-thickening-preserves-dimension
kind: claim
title: A projectional quasicentral support can be thickened across its multiplier projection without adding dimension
distinct_from:
  stw82-complemented-support-preserves-dimension: that theorem requires the generated ideal to be a direct summand; the present theorem permits proper essential generated ideals and uses a projectional quasicentral exhaustion instead of a central multiplier support.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that theorem characterizes projectional cuts for an already specified extension ideal; the present theorem constructs such cuts for the larger ideal L+C p from data lying entirely in the smaller ideal L.
  stw82-split-af-is-one-multiplier-projection-problem: that theorem handles full multiplier projections by a full corner; here p is allowed to be nonfull and the residual quotient A/L can be nonzero.
artifacts:
  - research/artifacts/stw82-quasicentral-support-thickening-audit-2026-08-30.md
---

Let `A` be a separable C*-algebra, let `p in M(A)` be a projection, and put

```text
L=closure(ApA),             K=A+C p,             J=L+C p.
```

Suppose `L` has an approximate unit of projections `(e_n)` satisfying

```text
norm([e_n,a])->0       for every a in A,
norm([e_n,p])->0.                                           (QST1)
```

Then

```text
dim_nuc(A+C p)=dim_nuc(A).                                 (QST2)
```

The hypothesis is strictly weaker in support geometry than complementation.
It can hold when `L` is proper and essential in `A`, so `L` has no nonzero
complementary ideal.  The mechanism is an exact thickening of projectional
cuts: block-diagonalize `e_n` relative to `p`, spectrally repair it to a
projection `r_n in L` commuting with `p`, and set

```text
q_n=p+(1-p)r_n.                                             (QST3)
```

Then `(q_n)` is a quasicentral approximate unit of projections for `J` in
`K`.  Thus

```text
0 -> J -> K -> A/L -> 0                                   (QST4)
```

is a quasidiagonal extension.  The quasidiagonal-extension maximum theorem,
the full-corner computation `dim_nuc(J)=dim_nuc(L)`, and endpoint
monotonicity give `(QST2)`.

There are genuinely noncomplemented dimension-positive examples.  Let `H`
be separable infinite-dimensional, let `B=K(H)~`, and take

```text
A=(B tensor K(H)) tensor C([0,1]),
p=e_11 tensor 1_(B(H)) tensor 1.
```

Then

```text
L=(K(H) tensor K(H)) tensor C([0,1])
```

is a proper essential ideal, and hence is not complemented.  Standard
finite-rank projections `P_n,Q_n`, with `e_11<=P_n`, give

```text
e_n=P_n tensor Q_n tensor 1,
```

which satisfy `(QST1)` and commute with `p` exactly.  Here
`dim_nuc(A)=1`, so `(QST2)` computes the adjoined algebra's nuclear dimension
as one despite the noncomplemented support.
