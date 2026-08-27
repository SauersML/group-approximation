---
rg: 2
id: affine-leavitt-active-root-aperiodicity-proof
kind: route
title: Kill finite character orbits with active elementary transvections
target: affine-leavitt-active-root-character-orbits-are-aperiodic
requires:
  - affine-leavitt-steinberg-mark-is-fd-invisible
---

Let `chi in M_hat` have finite `H`-orbit `O`.  The permutation action on
`O` is a finite-dimensional unitary representation of `H`, and composition
with `St_5(R)->H` is a finite-dimensional representation of `St_5(R)`.
The proof of `affine-leavitt-steinberg-mark-is-fd-invisible` applies in rank
five and says that every active elementary transvection `x_ij(A)` acts
trivially in this permutation representation.  Hence `chi` is fixed by all
such transvections.

For `r in A R` and `i!=j`, apply `x_ij(A)` to the module vector having `r`
in coordinate `j` and zero elsewhere.  The Steinberg action adds `A r=r`
in coordinate `i`.  Invariance of `chi` therefore gives

```text
chi(x_i6(r))=1.
```

Varying `i` and `r` shows that `chi` is trivial on all of `M`.  Property
`(T)` passes to quotients, so the image `H` of `St_5(R)` has a fixed
Kazhdan constant.  Each nontrivial orbit is infinite and its quasi-regular
representation has no invariant vector, giving the uniform bottom gap.

