---
rg: 2
id: clifford-phase-space-twisted-cocycle-proof
kind: route
title: Compare Clifford conjugation phases and associate three lifts
target: clifford-phase-space-curvature-is-a-twisted-f2-cocycle
requires: []
---

Conjugating `W(S_(gh)v)` by the curvature in `(CPC1)` in two ways gives

```text
b(a(g,h),S_(gh)v)
 = ell_(gh)(v) + ell_h(v) + ell_g(S_h v),
```

because conjugation by `W(a)` contributes `(-1)^b(a,-)`.  Nondegeneracy of
`b` uniquely determines `a(g,h)`, proving `(CPC3)`.

Now compare `(U_g U_h)U_k` and `U_g(U_h U_k)`.  Discarding scalar Weyl
phases, their Pauli labels are respectively

```text
a(g,h)+a(gh,k)
```

and

```text
S_g a(h,k)+a(g,hk).
```

Associativity proves `(CPC2)`.  Finally replace every lift by
`W(r_g)U_g`.  Moving `W(r_h)` past `U_g` applies `S_g`, while comparison
with `U'_(gh)=W(r_(gh))U_(gh)` adds `r_(gh)` (subtraction is addition over
`F_2`).  This is exactly `(CPC4)`.

Thus killing all tested Pauli labels is the linear equation
`delta_S r=a`.  The usual finite-dimensional solvability criterion gives
the left-nullspace formulation.  If multiplication triangles can be ordered
so each new triangle contains a previously unused lift variable with
coefficient the identity, solve for that variable recursively; this proves
the stated acyclic sufficient case.
