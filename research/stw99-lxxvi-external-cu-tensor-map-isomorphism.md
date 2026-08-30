---
rg: 2
id: stw99-lxxvi-external-cu-tensor-map-isomorphism
kind: claim
title: The external Cu tensor map is invertible for every pure C*-algebra
---

For every pure C\*-algebra `A`, the canonical external-product morphism

```text
Cu(A) tensor_Cu Cu(Z) -> Cu(A tensor_min Z)
```

is an isomorphism.

This is open.  It is not a formal consequence of abstract `Cu(Z)`-absorption:
`stw99-lxxvi-external-cu-tensor-map-is-the-only-gap` proves that it is exactly
the missing comparison between the Cu-category tensor product and the
minimal C\*-tensor product.

## Attempts

Continuity proves the assertion for sequential inductive limits once it is
known at every stage, by
`stw99-lxxvi-cu-regularity-passes-to-inductive-limits`.  The unresolved case
is therefore not repaired by simply choosing regular approximating blocks.
On the negative side, failure of injectivity can be detected on compact
elements by `stw99-lxxvi-compact-cancellation-counterexample-criterion`.
