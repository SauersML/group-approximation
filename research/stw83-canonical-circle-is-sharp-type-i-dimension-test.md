---
rg: 2
id: stw83-canonical-circle-is-sharp-type-i-dimension-test
kind: claim
title: The canonical circle graph family is a sharp type-I dimension test
distinct_from:
  stw83-canonical-circle-primitive-spectrum-independent-of-n: that computes the non-Hausdorff primitive topology; this records the exact nuclear-dimension consequence for STW Problem LXXXI.
  stw83-canonical-circle-toeplitz-dimension-two-bound: that proves the value is one or two; this identifies what either endpoint would mean for the type-I topological-dimension problem.
  stw99-problem-lxxxi-commutative-hereditary-dimension: that is the universal shadow-to-nuclear-dimension question; this isolates an explicit finite-graph test object satisfying its hypothesis.
---

For every `N>=1`, put

```text
A_N=C*(S^N tensor 1, K tensor C(T)).
```

Then `A_N` is separable and type I, and

```text
ctdim(A_N)=topdim(A_N)=1,
1<=dim_nuc(A_N)<=2.                                    (1)
```

It satisfies the hereditary commutative-shadow hypothesis of STW Problem
LXXXI.  Consequently,

```text
a positive answer to STW LXXXI  ==>  dim_nuc(A_N)=1
for every N,                                             (2)

dim_nuc(A_N)=2 for some N  ==>  STW LXXXI is false.      (3)
```

The standard type-I shortcuts do not decide between (2) and (3).
The algebra is not continuous trace because its primitive spectrum is
non-Hausdorff.  It is not subhomogeneous because its ideal
`K tensor C(T)` has infinite-dimensional irreducible representations.
Thus neither the continuous-trace nuclear-dimension formula nor the
subhomogeneous formula applies.

There is currently no theorem identifying nuclear dimension with
Brown--Pedersen topological dimension for arbitrary type-I algebras; the
exact relation is itself the unresolved one-dimensional type-I frontier in
Problem LXXXI.  Hence the computation `topdim(A_N)=1` is an exact reduction,
not a dimension-one proof.

**ESTABLISHED.**

DERIVATION
[[stw83-canonical-circle-type-i-test-proof]]
