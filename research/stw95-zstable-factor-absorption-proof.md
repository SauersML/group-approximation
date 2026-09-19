---
rg: 2
id: stw95-zstable-factor-absorption-proof
kind: route
title: Move the Jiang--Su tensor factor next to the absorbing coordinate
target: stw95-one-zstable-factor-forces-pure-product
requires: []
---

Suppose `A` is Z-stable; the other case follows by symmetry.  Associativity
and symmetry of the minimal tensor product give

```text
(A tensor_min B) tensor_min Z
  ~= (A tensor_min Z) tensor_min B
  ~= A tensor_min B.                                  (1)
```

The second isomorphism is the tensor product with `id_B` of an absorption
isomorphism `A tensor_min Z ~= A`.  It remains an isomorphism without any
exactness assumption on `B`, since its inverse is obtained by tensoring the
inverse absorption isomorphism with `id_B`.  Thus (1) proves Z-stability of
the product.

For a Z-stable algebra, the first-factor map into its Z-stabilization induces
an isomorphism on Cuntz semigroups.  Cuntz semigroup regularity implies that
the Cuntz semigroup is almost unperforated and almost divisible; equivalently,
the algebra is pure.  These are exactly the general, not necessarily simple,
definitions used in Problem XCV.  Hence `A tensor_min B` is pure.

Nothing in the argument uses nuclearity of `A` or `B`: nuclearity of `Z` is
already built into the unambiguous minimal tensor rearrangement, while
functoriality of tensoring an isomorphism supplies the only map-level step.
