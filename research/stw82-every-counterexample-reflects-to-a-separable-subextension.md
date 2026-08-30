---
rg: 2
id: stw82-every-counterexample-reflects-to-a-separable-subextension
kind: claim
title: Every failure of the extension maximum formula has a separable subextension witness
---

If an extension `0 -> I -> E -> D -> 0` violates

```text
dim_nuc(E) = max(dim_nuc(I), dim_nuc(D)),
```

then some separable exact subextension `0 -> I_0 -> E_0 -> D_0 -> 0`
violates the same inequality, with

```text
dim_nuc(I_0) <= dim_nuc(I),
dim_nuc(D_0) <= dim_nuc(D).
```

The finite-set separable-hull proof is
`stw82-counterexamples-reflect-to-separable-extensions`.
