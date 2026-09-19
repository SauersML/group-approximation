---
rg: 2
id: finite-lcs-product-sign-is-exact-or
kind: claim
title: A product of private LCS signs implements an exact finite marked OR
distinct_from:
  odd-selector-priority-decoding: that partitions an already available odd selector corner; this gives the finite standard-LCS presentation whose marked models are exactly the OR of finitely many branch models.
  one-hot-selector-parity-barrier: that forbids forcing exactly one negative selector by affine rows; this needs only odd parity and uses priority corners, so multiple negative selectors are harmless.
  culf-mastel-rstar-uniform-fano-cap-profile: that must first produce a finite menu containing a complete Fano-cap branch; this solves the subsequent finite OR over that menu but does not prove such a branch exists.
---

**ESTABLISHED FINITE OR COMPILER.**  Let `L_1,...,L_m` be finite binary
linear constraint systems, with solution groups `Gamma_i` and their standard
central signs `J_i`.  One can effectively construct a single finite LCS
`L_OR`, with solution group `Gamma_OR` and central sign `J`, such that:

1. if some `L_i` has a perfect representation in a tracial von Neumann
   algebra with `J_i=-1`, then `L_OR` has one with `J=-1`;
2. every representation of `Gamma_OR` in a tracial matrix ultraproduct for
   which the negative spectral projection of `J` is nonzero has, on a
   nonzero corner, a perfect marked representation of some `L_i`;
3. the same decoding holds in an arbitrary finite tracial algebra.  Hence
   the statement is exact, and matrix-ultraproduct soundness is inherited
   solely because nonzero corners of tracial matrix ultraproducts are again
   tracial matrix ultraproducts.

In particular,

```text
some branch has a perfect tracial model
   iff L_OR has a perfect tracial model,                         (LOR1)

no branch has a perfect matrix-ultraproduct model
   implies L_OR has none.                                       (LOR2)
```

The construction stays inside ordinary LCS syntax.  Give branch `i` a new
selector involution `Z_i`.  Replace each branch equation

```text
product_(x in I) x = J_i^b
```

by the homogeneous row

```text
product_(x in I) x Z_i^b = 1.                                  (LOR3)
```

For every selector `Z_i` and every payload variable `x` in every branch,
add a fresh variable `Y_(i,x)` and the row

```text
Z_i x Y_(i,x)=1.                                                (LOR4)
```

This is a neutral commutation gadget: it forces `[Z_i,x]=1`, and any
commuting pair extends uniquely by `Y_(i,x)=Z_i x`.  Finally add

```text
product_(i=1)^m Z_i=J.                                         (LOR5)
```

Thus all selectors commute, their product is the one standard solution-group
sign, and they commute with every branch payload.  No nonlinear predicate,
one-hot constraint, direct-sum algebra, or identified branch sign is used.

Consequently, once finitely many Fano-cap affine LCS branches have been
listed and at least one is known to carry the perfect source model, their
finite OR is no longer a compiler obstruction.  What remains in the
Culf--Mastel/Fano lane is producing such a complete finite branch menu (and
the fixed-language quantum reduction), not selecting one member of an
already valid menu.

