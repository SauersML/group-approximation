---
rg: 2
id: hilbert-hotel-prime-stably-finite-mf-black-hole-proof
kind: route
title: Use the ICC factor closure to force primeness and the MF radical to kill every quotient
target: hilbert-hotel-prime-stably-finite-mf-black-hole
requires:
  - hilbert-hotel-model-full-mf-radical
  - hilbert-hotel-cstar-total-invisibility
---

Countability of `H` makes `A=C*_r(H)` separable.  The canonical trace is
faithful, so all matrix amplifications of `A` are finite; hence `A` is stably
finite.  Infinitude of `H` makes `A` infinite-dimensional.

Simplicity and infinitude of `H` imply that `H` is ICC.  Therefore the weak
operator closure of `A` in its regular representation is the factor `L(H)`.
If `I` is a nonzero ideal of `A`, its weak closure is a nonzero weakly closed
ideal of `L(H)`, and hence is all of `L(H)`.  If two nonzero ideals `I,J`
satisfied `IJ=0`, separate weak continuity of multiplication would give

```text
L(H)L(H)=0,
```

which is impossible.  Thus `A` is prime.  A separable prime C-star algebra
is primitive, so `A` has a faithful irreducible representation.  The same
argument shows that every nonzero ideal meets every other nonzero ideal,
which is essentiality.

Total MF radical of `H` and nonamenability of the Kazhdan simple group give
that every star homomorphism `A->B` with `B` MF is zero.  If a nonzero
quotient `A/I` were MF, the quotient map would contradict this assertion.
Every separable quasidiagonal C-star algebra is MF, so no nonzero quotient is
quasidiagonal either.  Finite-dimensional C-star algebras are MF, which also
rules out nonzero finite-dimensional representations.

