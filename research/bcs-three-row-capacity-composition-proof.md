---
rg: 2
id: bcs-three-row-capacity-composition-proof
kind: route
title: Delete the maximal forbidden atom from the doubled target and compare the two capacity bounds
target: bcs-deficit-plus-three-row-cell-kills-source
requires:
  - maximal-forbidden-atom-has-a-named-positive-half
  - rectangular-three-row-cell-forces-double-target-capacity
  - non-ce-bcs-has-robust-approximate-energy-gap
---

On the reducing target `T`, the robust BCS gap and pigeonhole principle give
one forbidden atom `A` with

```text
tr(A)>=(beta/M)tr(T)-(C_B/M)sqrt(E_B).
```

Removing it gives `F=T-A`.  If `tr(T)<=2tr(E)+xi`, then

```text
tr(F)<=(2-2beta/M)tr(E)
       +(1-beta/M)xi+(C_B/M)sqrt(E_B).
```

The rectangular three-row theorem applied to coefficient contractions
through this same `F` gives the reverse lower bound

```text
tr(F)>=2tr(E)-10sqrt(tr(E))epsilon_0
                    -2sqrt(tr(E))epsilon_1-4eta^2.
```

Their difference is the displayed carrier inequality `(BDT5)`.  In the
perfect infinite BCS model `A=0`, and the ordinary rectangular Leavitt cell
has exactly doubled target capacity, so the construction remains perfectly
complete there.
