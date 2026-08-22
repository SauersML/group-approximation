---
rg: 2
id: nonhyperlinear-from-amenable-group-basis-sl3
kind: route
title: Identify the automorphic group-basis crossed product with a semidirect-product group factor
target: non-hyperlinear-group
requires:
  - amenable-group-basis-sl3-envelope
  - non-ce-property-t-equivalence-relation-exists
---

For an action of `SL_3(Z)` by group automorphisms of `K`, the canonical
unitaries satisfy exactly the semidirect-product relations, and Fourier
expansion gives a trace-preserving isomorphism

```text
L(K) rtimes SL_3(Z) ~= L(K rtimes SL_3(Z)).
```

If the latter were Connes embeddable, so would be every trace-preserving von
Neumann subalgebra.  The embedding `(AGB1)` of the fixed non-CE factor rules
this out.  Hence `K rtimes SL_3(Z)` is a non-hyperlinear countable group (and
the effective hypotheses in the claim give the preferred recursively
presented/finitely presented upgrade).

