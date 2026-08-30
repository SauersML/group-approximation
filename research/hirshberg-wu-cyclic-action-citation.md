---
rg: 2
id: hirshberg-wu-cyclic-action-citation
kind: route
title: Import the uniform bounds for integer and finite-group actions
target: hirshberg-wu-cyclic-action-bound
requires: []
---

Hirshberg--Wu,
[*The nuclear dimension of C-star-algebras associated to
homeomorphisms*](https://doi.org/10.1016/j.aim.2016.08.022), Advances in
Mathematics 304 (2017), 56--89, Theorem 5.1, proves `(HWC1)` for every
homeomorphism of a finite-dimensional locally compact metrizable space.

For `(HWC2)`, apply their Theorem 3.4 to the action of an arbitrary finite
group `F`.
The action has uniformly compact orbits.  Every stabilizer is finite, so its
group C-star-algebra is finite dimensional and has nuclear dimension zero.
The quotient map `X -> X/F` is open and finite-to-one, whence
`dim(X/F)=dim(X)=r` by their Proposition 1.6.  Theorem 3.4 therefore gives

```text
dim_nuc(C(X) rtimes F)+1 <= (r+1)(0+1),
```

which is `(HWC2)`.  Neither estimate depends on the particular action or, in
the finite case, on the order or isomorphism type of `F`.
