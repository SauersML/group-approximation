---
rg: 2
id: andrew-guerch-hughes-theorem-e-citation
kind: route
title: Apply Andrew--Guerch--Hughes Theorem E
target: relatively-hyperbolic-polycyclic-suspensions-in-ac-vnil
requires: []
---

Source: Naomi Andrew, Yassine Guerch, and Sam Hughes,
*Automorphisms of relatively hyperbolic groups and the Farrell--Jones
conjecture*, Mathematische Annalen 395, article 89 (2026),
doi:10.1007/s00208-026-03431-7.

Theorem E states directly that if `G` is one-ended or virtually
torsion-free and is hyperbolic relative to finitely many conjugacy
classes of virtually polycyclic subgroups, then, for every
`Phi in Aut(G)`,

```text
G semidirectProduct_Phi Z belongs to AC(VNil).
```

There is no hypothesis that `Phi` preserve each peripheral conjugacy
class.

Section 1.3 states that every group in `AC(VNil)` satisfies
Farrell--Jones. Under the paper's convention from Section 1, this is the
fibred conjecture with respect to virtually cyclic subgroups, separately
for `X in {A,K,L}`.

Theorem 5.24 supplies the proof's virtual-neatness input: for a group
hyperbolic relative to slender peripherals and every automorphism
`Phi`, there is `N > 0` such that

```text
Per(Phi) = Fix(Phi^N),
```

and this subgroup is finitely generated. Virtually polycyclic groups
are slender. The proof of Theorem E then applies the same acylindrical
JSJ-tree argument as Theorem A, replacing periodic vertex groups by
fixed subgroups of powers, and obtains `AC(VNil)` directly. QED
