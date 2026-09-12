---
rg: 2
id: literal-mf-radical-has-no-infinite-kazhdan-subgroup-proof
kind: route
title: Fix a vertex in the Bass--Serre tree of the finite Clifford-block amalgam
target: literal-mf-radical-has-no-infinite-kazhdan-subgroup
requires:
  - literal-mf-radical-is-unsquared-defect
  - literal-lamp-kernel-clifford-block-amalgam
---

Write `d=tct^(-1)` and `u=[d,v_1]`.  The element `d` belongs to the literal
lamp kernel `N_E`, and `N_E` is normal in `E`; hence its commutator with
`v_1` belongs to `N_E`.  Normality then gives

```text
D=<<u>>^E <= N_E.                                      (LKT1)
```

By `literal-lamp-kernel-clifford-block-amalgam`, `N_E` is the fundamental
group of the star-shaped graph of groups whose vertex groups are the
order-`512` groups `ClLamp_i(8)` and whose edge groups are their identified
central order-two subgroups `<w>`.  Its Bass--Serre action is without
inversions and every vertex stabilizer is conjugate to one of those finite
block groups.

Let `H<=D` have property `(T)`.  Property `(T)` implies Serre's fixed-point
property `FA`, so the restricted action of `H` on the Bass--Serre tree fixes
a vertex.  Therefore `H` lies in the corresponding vertex stabilizer and is
finite.  If `H` is also torsion-free, it is trivial.  Equation `(LKT1)` and
the exact radical computation finish the claim.
