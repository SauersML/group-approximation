---
rg: 2
id: stw82-one-dimensional-middle-forces-maximum-proof
kind: route
title: Collapse the extension inequality at the two-colour ceiling
target: stw82-one-dimensional-middle-forces-maximum
requires:
  - stw82-every-counterexample-reflects-to-a-separable-subextension
---

Nuclear dimension does not increase on ideals or quotients, so

```text
r=max(dim_nuc(I),dim_nuc(D)) <= dim_nuc(E) <= 1.       (M2)
```

If `r=1`, (M2) is already equality.  Suppose toward a contradiction that
`r=0` and the formula fails.  By
`stw82-every-counterexample-reflects-to-a-separable-subextension`, there is
a separable exact subextension

```text
0 -> I_0 -> E_0 -> D_0 -> 0                           (M3)
```

which still fails the formula and whose endpoint dimensions are zero.
The reflection theorem's finite obstruction says this failure at endpoint
maximum zero forces `dim_nuc(E_0)>0`.

The separable dimension-zero characterization says that `I_0` and `D_0`
are AF.  AF algebras are closed under extensions, so `E_0` is AF and has
nuclear dimension zero, contradicting that (M3) fails.  These are the only
cases.

The imported inputs are precisely Winter--Zacharias' permanence of nuclear
dimension for ideals and quotients, the repository's separable reflection
theorem, and the classical facts that a separable C*-algebra has nuclear
dimension zero exactly when it is AF and that AF algebras are extension
closed.  No nuclear-dimension extension upper bound is used.
