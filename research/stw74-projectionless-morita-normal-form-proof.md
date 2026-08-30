---
rg: 2
id: stw74-projectionless-morita-normal-form-proof
kind: route
title: Pass both ways between a bad unital corner and its projectionless full hereditary model
target: stw74-counterexamples-are-exactly-projectionless-morita-models
requires:
  - stw74-counterexamples-are-unstably-projectionless
---

Starting with a counterexample `A`, the required claim supplies a nonzero
full projectionless hereditary subalgebra `D`.  It may be chosen generated
by one positive element and is therefore sigma-unital; when `A` is
separable, so is `D`.  Brown stabilization gives

```text
D tensor K ~= A tensor K.                                   (1)
```

The stabilized unit gives a nonzero projection on the left.  Every nonzero
projection there is properly infinite by the stabilized-projection theorem.
Pure infiniteness is invariant under stable isomorphism and hereditary
Morita equivalence, so `D` is not purely infinite.  This proves `(NF)`.

Conversely, suppose `D` satisfies `(NF)` and choose a nonzero projection
`p in D tensor K`.  The corner

```text
A_p=p(D tensor K)p
```

is nonzero, unital, and simple.  Each of its nonzero projections is a
nonzero projection of `D tensor K`, hence is properly infinite and in
particular infinite.  The projection `p` is full by simplicity, so `A_p` is
Morita equivalent to `D`.  If `A_p` were purely infinite, Morita invariance
would make `D` purely infinite, contrary to `(NF)`.  Thus `A_p` is an
LXXIV counterexample.

No nuclearity is used.  Nuclearity and separability pass both ways through
hereditary subalgebras and Morita equivalence, so the same equivalence holds
with either qualifier imposed.
