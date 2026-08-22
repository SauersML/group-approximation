---
rg: 2
id: nonzero-diagonal-clifford-type-closes-all-six-local-cycles
kind: claim
title: One nonzero deepest-layer Clifford type closes all six local denominator cycles
distinct_from:
  sl3-depth-two-clifford-fiber-has-thirty-six-types: that enumerates the type set; this exhibits a nontrivial type which survives every local directional compatibility test.
  six-parahoric-finite-fiber-folds-remain-amenable: that permits arbitrary abstract fiber recycling; this gives an arithmetic character type, realized at every dyadic depth, whose local recycling is canonical.
  native-parahoric-triangle-kills-all-corrector-gauges: that kills a common multiplicity corrector after a carrier is decoded; this concerns only the deepest-kernel character orbit and leaves its stabilizer cocycle and multiplicity extension unspecified.
---

Let

```text
X=diag(1,-1,0) in sl_3(Z/4Z),                           (DCT1)
```

and let `f_*` be its `SL_3(Z/4Z)` coadjoint orbit.  The exhaustive orbit
table gives

```text
|f_*|=2688,       |Stab_(SL_3(Z/4))(X)|=16.             (DCT1a)
```

For every `a>=4`,
the corresponding nontrivial character of

```text
N_a=ker(SL_3(Z/2^a)->SL_3(Z/2^(a-2)))
```

is an exact-conductor type: every irreducible constituent of its induction
to `SL_3(Z/2^a)` has conductor `a`.

The type `f_*` is compatible with all six Weyl-conjugate denominator
directions.  Indeed every coweight diagonal commutes with `X`, while a Weyl
change of chart sends `X` to a signed permutation of its diagonal entries,
which lies in the same `SL_3(Z/4Z)` orbit.  Hence each of the six local type
transitions has a loop at `f_*`, and every inverse, triangle, and closed
hexagon word closes exactly on that loop.

Consequently there is no forbidden transition cycle at the level of the
thirty-six deepest-layer orbit labels.  A finite local obstruction must use
the stabilizer's projective extension/Mackey cocycle or its multiplicity
representation, not merely the coadjoint type.  Alternatively it must
remember more than two congruence layers.  This does not construct a full
arithmetic leak: simultaneous extension of the six local characters on one
matrix carrier is the remaining issue.
