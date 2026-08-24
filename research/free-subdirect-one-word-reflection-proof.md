---
rg: 2
id: free-subdirect-one-word-reflection-proof
kind: route
title: Lift the subdirect actor and isolate all coordinate orbits diagonally
target: free-subdirect-products-have-one-word-mf-reflections
requires:
  - finite-orbit-subgroups-inherit-internal-mf-reflections
  - perfect-mf-reflection-over-residually-p-actor
  - binary-leavitt-unit-word-problem-decidable
  - internal-mf-reflection-subgroup-lattice
---

Apply the finite-product reflection to the free actors `F_(r_i)`.  Its base
is

```text
B=product_i U^(F_(r_i)),
```

and take `K_S=B semidirectProduct S`.  Surjectivity of every coordinate
projection means that the `S`-action has exactly one orbit on each coordinate
family.  The finite-orbit theorem therefore makes `K_S` finitely generated
and shows that the product of one seed involution from each family is a
single involution `delta_S` normally generating `B`.

Every finite-rank free group is torsion-free, characteristic-zero linear,
and residually `p` for every prime.  These properties pass to finite products
and subgroups, so they hold for `S`.  The group `U` is perfect, hence the
restricted direct-product base `B` is perfect.  Apply
`perfect-mf-reflection-over-residually-p-actor` separately for every prime.
This gives `(FSP3)`, `(FSP4)`, all residual identities, and all completion
isomorphisms.  The remaining target, closure, and finite-index lattice
statements are the finite-orbit and subgroup-correspondence formulas.

The embedding `(FSP1)` gives a direct word-problem algorithm for `S`: replace
a word in its fixed generators by the corresponding tuple of free-group
words and freely reduce every coordinate.  For `K_S`, scan a word while
maintaining that actor tuple and one finite coordinate dictionary for each
restricted base family.  The free-group algorithms combine addresses and
`binary-leavitt-unit-word-problem-decidable` reduces their `U`-values.  The
word is trivial exactly when the actor tuple is trivial and every dictionary
is empty.
