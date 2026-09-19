---
rg: 2
id: stw99-lxxvi-compact-cancellation-counterexample-criterion
kind: claim
title: Projection cancellation after Z-stabilization gives a counterexample criterion for Problem LXXVI
distinct_from:
  stw95-cu-z-tensor-counterexample: that creates new compact K0 classes from a K1 cross term in a tensor square; tensoring with Z creates no such K-theory cross term, and this criterion instead detects collapse of old compact classes.
---

Let `A` be a C\*-algebra and let `p,q` be projections over `A` such that

```text
[p] != [q] in Cu(A),
[p tensor 1_Z] = [q tensor 1_Z] in Cu(A tensor_min Z).
```

Then `A` is not Cuntz semigroup regular.  In particular, these hypotheses
hold if

1. `p` and `q` have the same `K_0(A)` class but are not Murray--von Neumann
   equivalent; and
2. projections cancel over `A tensor_min Z`.

Therefore a pure algebra satisfying conditions 1 and 2 would refute Problem
LXXVI.  No Kunneth theorem or identification of the K-theory of the tensor
product is needed.

Condition 1 is only a first filter.  Under the cancellation hypothesis in
condition 2, the stabilized projections are Murray--von Neumann equivalent,
so `[p]=[q]` already in the `K_0` group of their generated ideal by the
KK-equivalence `J -> J tensor Z`.  More generally this conclusion holds when
that stabilized ideal is stably finite, by
`stw99-lxxvi-ideal-local-k0-protection`.  Without finiteness, equality of Cu
classes for infinite projections need not imply equality in `K_0`.
