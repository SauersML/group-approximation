---
rg: 2
id: stw82-one-dimensional-middle-forces-maximum-proof
kind: route
title: Collapse the extension inequality at the two-colour ceiling
target: stw82-one-dimensional-middle-forces-maximum
requires: []
---

Nuclear dimension does not increase on ideals or quotients, so

```text
r=max(dim_nuc(I),dim_nuc(D)) <= dim_nuc(E) <= 1.       (M2)
```

If `r=1`, (M2) is already equality.  If `r=0`, separability and the
dimension-zero characterization say that `I` and `D` are AF.  AF algebras
are closed under extensions, so `E` is AF and hence has nuclear dimension
zero.  This again gives equality.  These are the only cases.

The two imported inputs are precisely Winter--Zacharias' permanence of
nuclear dimension for ideals and quotients and the classical facts that a
separable C*-algebra has nuclear dimension zero exactly when it is AF and
that AF algebras are extension closed.  No nuclear-dimension extension
upper bound is used.
