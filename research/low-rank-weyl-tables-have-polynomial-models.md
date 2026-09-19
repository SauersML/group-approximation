---
rg: 2
id: low-rank-weyl-tables-have-polynomial-models
kind: claim
title: Low approximate-rank Weyl tables have polynomial-size balanced canonical-moment models
distinct_from:
  dense-offdiagonal-packet-has-linear-dimensional-average-models: that is the rank-one complementary-prefix instance; this works for every Boolean table after a low-rank edit.
---

**ESTABLISHED.**

Let `K in M_(D x D)(F_2)`.  Suppose `K'` differs from `K` on at most an
`epsilon` fraction of entries and

```text
rank_(F_2)(K')=r.
```

Then there is a balanced unitary model of dimension

```text
d <= 32 · 2^max(r,2) D^2                              (LAR1)
```

with involutions `X_u,Y_v,J` such that `tr(J)=0`, `J` is central,

```text
[X_u,X_u']= [Y_v,Y_v']=1,
tr(X_u)=tr(Y_v)=0,
tr(X_u^*X_u')=delta_(u,u'),
tr(Y_v^*Y_v')=delta_(v,v'),
tr(X_u^*Y_v)=0,                                         (LAR2)
```

and the uniform mean squared normalized-HS defect of

```text
[X_u,Y_v]=J^(K_(u,v))                                   (LAR3)
```

is at most `2 epsilon`.  The central mark remains maximally separated:
`||J-I||_2^2=2`.

Combining this with
`bounded-prefix-decision-cost-forces-bounded-approximate-rank` gives a
general collapse theorem for classical prefix Weyl tests.  At any fixed
target error, their pairing tables admit models of size polynomial in the
number of labels, while the exact nondegenerate packet asks for dimension
exponential in that number.  Letting the target error tend to zero slowly
still produces an approximate-model sequence.  Thus a dimension overflow
argument cannot be made robust merely by replacing equality with another
bounded-average prefix predicate; it needs a test family with genuinely
growing approximate rank or a separate amplifier which charges the deep
cells.
