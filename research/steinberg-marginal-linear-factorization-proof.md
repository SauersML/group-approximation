---
rg: 2
id: steinberg-marginal-linear-factorization-proof
kind: route
title: Apply finite-dimensional kernel-factorization duality to the chord rows
target: steinberg-marginal-split-is-linear-factorization
requires:
  - steinberg-cycles-have-big-cell-chord-coordinates
  - steinberg-fox-chord-actions-are-explicit
  - steinberg-tree-cuts-are-five-marginals
---

For linear maps between finite-dimensional vector spaces,

```text
ker R subset ker M   iff   M factors through R.        (SML2)
```

Indeed, in the forward direction define `L` on `im R` by `L(Rf)=M(f)` and
extend it linearly to the codomain of `R`; the reverse direction is
immediate.  This proves item 1.

The common kernel of `R` and `M` is the kernel of their stacked map.  That
kernel is zero exactly when the stacked map is injective, equivalently when
it has a left inverse.  This proves item 2.

If `M=LR`, then `(R,M)f=(Rf,LRf)`, so `(R,M)` is injective exactly when `R`
is injective.  Conversely, if `R` is injective then it has a left inverse,
and both marginal implications hold.  This proves item 3.
