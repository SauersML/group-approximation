---
rg: 2
id: stw99-xciv-local-fd-everywhere-would-make-r-nuclear-proof
kind: route
title: Convert local finite-dimensional distance zero into CPAP and contradict a nonexact matrix product
target: stw99-xciv-some-finite-tuple-has-positive-fd-radius
requires: []
artifacts:
  - research/artifacts/stw99-xciv-commutant-capacity-audit-2026-08-30.md
---

Suppose for contradiction that `alpha_R(F)=0` for every finite `F subset R`.
Fix such an `F` and `epsilon>0`.  Choose a unital finite-dimensional
subalgebra `E subset R` within `epsilon` of every element of `F`.

Finite-dimensional C*-algebras are injective operator systems.  Therefore
the identity map on `E` extends to a unital completely positive retraction

```text
P:R->E.
```

Let `i:E->R` be the inclusion.  For `a in F`, choose `b_a in E` with
`||a-b_a||<epsilon`.  Since `P(b_a)=b_a`,

```text
||iP(a)-a||
 <=||P(a-b_a)||+||b_a-a||
 <2 epsilon.                                             (2)
```

Thus the identity of `R`, regarded as a C*-algebra, has point-norm
completely positive approximations through finite-dimensional algebras.
This is CPAP, so `R` would be nuclear.

The hyperfinite II1 factor is not nuclear as a C*-algebra.  One concrete
reason is that it contains a unital copy of

```text
product_(n>=1) M_n.
```

Indeed choose orthogonal nonzero projections `p_n` summing strongly to one,
put a unital `M_n` in each corner `p_n R p_n`, and take bounded strong block
sums.  This is an isometric star homomorphism from the product into `R`.
The product of matrix algebras of unbounded size is not exact (the standard
Wassermann matrix-product obstruction), whereas exactness passes to
C*-subalgebras.  Hence `R` is not exact and therefore not nuclear.

This contradiction proves that some finite `F` has `alpha_R(F)>0`; taking
`c=alpha_R(F)` gives `(1)`.  The argument is purely operator norm.  The
usual hyperfinite `2`-norm approximation does not yield the retractions in
`(2)` with point-norm control.
