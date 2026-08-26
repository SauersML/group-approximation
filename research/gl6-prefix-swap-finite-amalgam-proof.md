---
rg: 2
id: gl6-prefix-swap-finite-amalgam-proof
kind: route
title: Amalgamate the surviving GL6 child with the coarse prefix reflection
target: gl6-cross-return-plus-one-prefix-swap-retains-fine-carrier-gauge
requires:
  - private-middle-swap-crosses-returned-morita-branches-but-has-gl6-model
  - literal-prefix-three-root-swap-retains-typed-carriers
---

The first dependency supplies a finite group `G_6` and a nonidentity
involution `c`.  The second supplies a finite typed realization of the
three-root prefix word.  Taking every leaf space one-dimensional makes its
partial swap, its coarse and fine packet permutations, and its carrier
involutions signed permutation matrices.  They generate a finite group
`H`, and the coarse involution `r_e` is nonidentity.

We use only the following elementary finite-amalgam observation.  If `A,B`
are finite groups and `a in A`, `b in B` are nontrivial involutions, then
their left regular actions are fixed-point-free permutations: every orbit
of `a` or `b` has size two.  Repeat the regular action of `A` exactly
`|B|` times and that of `B` exactly `|A|` times.  Both now act on

```text
L=|A||B|
```

points, and `a,b` are each products of `L/2` disjoint transpositions.
They are therefore conjugate by an explicit bijection of their two-element
orbits.  Conjugate the second regular image by that bijection.  The two
faithful finite permutation images now agree on the named involution, and
the subgroup which they generate inside `Sym(L)` is finite.

Apply this with

```text
A=G_6,       a=c,       B=H,       b=r_e.              (GPSP1)
```

This proves that the complete six-coordinate table and the literal prefix
table have a simultaneous finite exact realization satisfying `c=r_e`.
Faithfulness on `A` proves that the marked child survives.

The construction glues only the named order-two source occurrence.  It
does not identify the source and target packet identities inside the typed
prefix model.  The explicit model from
`literal-prefix-three-root-swap-retains-typed-carriers` therefore retains
`(GPS4)` verbatim.  Since the fine reflection/support row in `(GPS5)` is
exactly the datum absent from that model, it is not a consequence of the
combined occurrence table.  The rank contradiction from
`one-coarse-to-fine-prefix-isometry-closes-the-reservoir` cannot be invoked
without one further same-carrier authentication row.
