---
rg: 2
id: avfree-sofic-proof
kind: route
title: Apply amenable-extension closure of soficity
target: abelian-by-virtually-free-groups-are-sofic
requires: []
---

The kernel `A` is abelian and therefore amenable.  A virtually free group is
residually finite: a finite-index free subgroup is residually finite, and
residual finiteness passes from a finite-index subgroup to the whole group by
taking the core of a separating finite-index subgroup.  Hence `Lambda` is
sofic.

Use the standard amenable-extension theorem for sofic groups: if
`1 -> N -> G -> Q -> 1` is exact, `N` is amenable, and `Q` is sofic, then
`G` is sofic.  Applying it to

```text
1 -> A -> A semidirect Lambda -> Lambda -> 1
```

proves the claim.  No finite generation assumption on the abelian kernel is
needed.
