---
rg: 2
id: torsion-free-mf-seed-via-higman-four-cycle
kind: route
title: Use marked point-operator-norm collapse of Higman's four-cycle
target: torsion-free-fp-ah-mf-radical-seed
requires:
  - higman-four-cycle-intrinsic-mf-seed
---

After the candidate node is established internally, take

```text
E=Hig,       d=g_0.
```

Its internalized group-theoretic clauses give finite presentation,
torsion-freeness, acylindrical hyperbolicity, and `d!=1`.  The marked
operator-norm collapse gives `d in Rad_MF(E)`, in fact
`Rad_MF(E)=E`.  These are exactly the clauses of the intrinsic seed.

The literature facts listed in the candidate are background only.  This
route is not available to the final no-literature Lean endpoint until those
facts and the marked collapse have all been internalized.
