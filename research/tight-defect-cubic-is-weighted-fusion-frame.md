---
rg: 2
id: tight-defect-cubic-is-weighted-fusion-frame
kind: claim
title: The tight-defect cubic is exactly a weighted fusion-frame identity
distinct_from:
  tight-defect-column-solves-algebraic-projection-crt: that uses the cubic identity to manufacture a projection; this identifies the cubic completely in terms of the negative incidence projections and gives an if-and-only-if criterion.
  affine-frobenius-tight-defect-column-frame: that asks for a packet construction preserving the strict verifier budget; this is the operator-algebraic normal form which every such construction must satisfy.
---

**ESTABLISHED.**  Let `q_1,...,q_r` be projections, let
`A_1,...,A_r` be self-adjoint unitaries with `[A_i,q_i]=0`, and assume the
shared-involution compatibility equations `(SIC3)`.  Put

```text
e_i=(1-A_i)/2,                 r_i=e_iq_i,              (TFF1)
```

so every `r_i` is a projection.  For positive weights `w_i`, let `D_w` be
the row with columns

```text
(D_w)_i=sqrt(w_i)(q_i-A_iq_i)=2sqrt(w_i)r_i.           (TFF2)
```

Let

```text
p=join_i r_i,                  S=sum_i w_i r_i.         (TFF3)
```

Then, for `lambda>0`,

```text
D_w D_w^* D_w=lambda D_w                                (TFF4)
```

holds if and only if

```text
S=(lambda/4)p.                                          (TFF5)
```

Thus the proposed cubic condition is exactly the assertion that the
negative incidence projections form a weighted tight fusion frame for
their join.  Repeating the `i`th column `m_i` times is precisely the special
case `w_i=m_i`; it changes no subspace and supplies no operation beyond
integer weighting.

If there are only two nonzero incidence projections, positive weights can
make them tight only when they are equal or orthogonal.  In particular,
column repetition cannot tighten a generic pair of nonorthogonal distinct
incidence defects.
