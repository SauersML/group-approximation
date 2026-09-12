---
rg: 2
id: finite-group-intertwiner-shrinkage-formula
kind: claim
title: Shrinkage of a finite-group intertwiner space is exactly weighted multiplicity excess
---

Let `H` be a finite group and let `V,W` be finite-dimensional complex unitary
`H`-representations.  Write their isotypic decompositions as

```text
V = directSum_lambda S_lambda tensor C^(m_lambda),
W = directSum_lambda S_lambda tensor C^(n_lambda),
d_lambda = dim S_lambda,
```

and let

```text
K = Hom_H(V,W) <= Hom(V,W).
```

For a subspace `X<=V`, write

```text
K(X) = span { T x : T in K, x in X }.
```

Then the maximal shrunk-subspace deficiency of `K` is

```text
max_(X<=V) (dim X - dim K(X))
  = sum_lambda d_lambda (m_lambda-n_lambda)_+.          (FGS1)
```

In particular, if `dim V=dim W=d`, then

```text
max_X (dim X-dim K(X))
  = (1/2) sum_lambda d_lambda |m_lambda-n_lambda|.      (FGS2)
```

Thus an exact finite-group intertwiner space has a `gamma d`-shrunk subspace
if and only if the two normalized isotypic multiplicity profiles differ by
weighted `L1` mass at least `2 gamma`.

This converts noncommutative-rank shrinkage for a semisimple intertwiner space
into a completely explicit integer/multiplicity invariant.  Operator scaling
can still discover the witness, but in this finite-group special case it is
not hiding any more exotic obstruction than isotypic multiplicity imbalance.
