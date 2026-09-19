---
rg: 2
id: stw82-kirchberg-stably-commutative-citation
kind: route
title: Apply the stable-isomorphism form of the Kirchberg-by-commutative extension theorem
target: stw82-kirchberg-by-stably-commutative-maximum
requires: []
artifacts:
  - research/artifacts/stw82-projectional-cut-obstruction-audit-2026-08-30.md
---

Evington--Ng--Sims--White,
[*Nuclear dimension of extensions of commutative C*-algebras by Kirchberg
algebras*](https://arxiv.org/abs/2409.12872v2), Corollary 4.2, states exactly
the following.  If `J` is a stable Kirchberg algebra, `X` is a compact metric
space, `A` is stably isomorphic to `C(X)`, and

```text
0 -> J -> E -> A -> 0
```

is essential, then

```text
dim_nuc(E)=max(1,dim(X)).                              (KSC1)
```

The source proves this by Lemma 4.1: stability of `J` converts the given
extension, up to stable isomorphism of its middle algebra, into an essential
extension with quotient `C(X)`.  Theorem B then gives `(KSC1)`.  Nuclear
dimension is invariant under stable isomorphism.

For the endpoint formulation, every stable Kirchberg algebra has nuclear
dimension one, while stable-isomorphism invariance and the commutative
dimension theorem give

```text
dim_nuc(A)=dim_nuc(C(X))=dim(X).
```

Consequently `(KSC1)` is precisely the endpoint maximum formula.  The
essentiality, stable Kirchberg ideal, compact metrizability of `X`, and stable
isomorphism of the quotient are all retained; the cited theorem makes no
claim here for a nonessential extension or for the reversed ideal--quotient
direction.
