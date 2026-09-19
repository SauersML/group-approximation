---
rg: 2
id: a5-d10-parity-table-proof
kind: route
title: Restrict the A5 character table to rotations and reflections
target: a5-d10-restriction-keeps-parity-charge
requires: []
---

The two conjugacy classes of nonidentity rotations in `D_10` are the two
order-five classes of `A_5`, while every reflection in `D_10` is a double
transposition.  On these classes, the irreducible `A_5` characters have
values

```text
dim       reflection       the two rotation classes
1              1                    1,1
3             -1                  phi,phibar
3'            -1                phibar,phi
4              0                   -1,-1
5              1                    0,0,
```

where `phi=(1+sqrt(5))/2` and `phibar=(1-sqrt(5))/2`.  The dihedral
characters are `1`, `epsilon`, and the two real rotation pairs with
reflection value zero.  Comparing dimensions and these three kinds of
class values gives `(ADR2)`.

Every vector in `(ADR2)` has even total multiplicity on
`{epsilon,rho_1,rho_2}`, proving `(ADR3)`.  Equation `(ADR5)` follows by
adding the three middle restriction vectors, and `(ADR6)` is the final row
of `(ADR2)`.
