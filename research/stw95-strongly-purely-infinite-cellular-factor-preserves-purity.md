---
rg: 2
id: stw95-strongly-purely-infinite-cellular-factor-preserves-purity
kind: claim
title: Exact strongly purely infinite factors and cellular filtrations tensor purely
distinct_from:
  stw95-one-zstable-factor-forces-pure-product: that assumes one entire factor absorbs Z; the direct theorem here instead assumes an exact strongly purely infinite factor, and the cellular theorem assumes exactness of the other factor plus strong pure infiniteness only of the successive ideal quotients, with no Z-absorption hypothesis or conclusion.
  stw95-transfinite-ash-layered-factor-preserves-purity: that uses nuclear stably finite ASH cells and permits a nonexact tensor factor under simplicity or residual stable finiteness; this uses purely infinite cells and an exact tensor factor, with no nuclearity or quotient-finiteness hypothesis.
  stw95-scattered-primitive-local-product-test: that extracts simple layers from a scattered primitive spectrum and assumes those layers are nuclear; the filtration here is supplied directly, its cells need not be simple or nuclear, and their primitive spaces may be nondiscrete zero-dimensional spaces.
  stw95-central-block-closure-of-tensor-pure-seeds: that decomposes both factors as complemented central c0-block sums; this permits non-split, noncentral transfinite extensions.
  stw95-transfinite-exact-filtration-reduction: that leaves purity of every successor-layer tensor product as a hypothesis; this theorem discharges all those local hypotheses uniformly from strong pure infiniteness, or from pure infiniteness plus the ideal property.
  stw95-semisplit-successor-filtration-reduction: that is an abstract local-to-global theorem for arbitrary pure cell products; this supplies those products from exact strong pure infiniteness and also records the complementary exact-other-factor case where the successor extensions need not split.
artifacts:
  - research/artifacts/stw95-strongly-purely-infinite-cellular-tensor-audit-2026-08-30.md
---

First, let `C` be a separable exact strongly purely infinite C*-algebra and
let `D` be any separable C*-algebra.  Then

```text
C tensor_min D
```

is strongly purely infinite and therefore pure.  In particular, this is a
positive class for Problem XCV whenever `D` is pure.  It is enough that `C`
be exact, purely infinite, and have the ideal property; equivalently in the
separable purely infinite setting, `Prim(C)` may be required to have a basis
of compact-open sets.

There is also a transfinite cellular version.  Let `A` and `B` be separable
C*-algebras and suppose that `B` is exact.  Let
`(I_alpha)_(alpha<=gamma)` be a continuous increasing filtration of `A` by
closed ideals, indexed by an arbitrary ordinal, such that

```text
I_0=0,                 I_gamma=A,
I_lambda=closure(union_(alpha<lambda) I_alpha)
```

at every limit ordinal.  Assume every successor cell

```text
L_alpha=I_(alpha+1)/I_alpha
```

is strongly purely infinite.  Then

```text
A tensor_min B
```

is pure.  The algebra `A` is itself pure, so if `B` is pure this is a
positive class for STW Problem XCV.

There is a complementary version with no exactness assumption on `B`.
Suppose instead that every `L_alpha` is exact and strongly purely infinite,
and that each successor quotient map

```text
I_(alpha+1) -> L_alpha
```

has a cpc section.  Then `A tensor_min B` is pure for every separable
C*-algebra `B`.  Again `A` is pure, so every pure `B` gives a Problem XCV
pair, including nonexact `B`.

The direct conclusion remains valid when `C` is instead assumed exact,
purely infinite, and to have the ideal property.  Likewise, the cellular
conclusions hold when the strong-pure-infiniteness hypothesis on every
`L_alpha` is replaced by pure infiniteness plus the ideal property (while
retaining exactness of the cells in the semisplit version).  Since these
algebras are separable, the ideal-property assumption can equivalently be
replaced by a basis of compact-open sets in the relevant primitive ideal
spaces.

No cell is required to be simple, nuclear, Z-stable, ASH, or locally
subhomogeneous.  In the exact-`B` version the successor extensions need not
even be semisplit; in the complementary version they need only be cpc
semisplit, not split by *-homomorphisms or central summands.
