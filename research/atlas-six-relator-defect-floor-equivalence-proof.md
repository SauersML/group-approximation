---
rg: 2
id: atlas-six-relator-defect-floor-equivalence-proof
kind: route
title: Convert the scalar six-relator floor to and from the five-row lift
target: atlas-five-row-operator-phase-lift
requires:
  - atlas-six-relator-regular-face-defect-floor
  - atlas-five-row-blowup-branch-is-impossible
---

Write

```text
A(U)=sum_(j in {0,11,30,44,55})||rho(z_j)U||_2^2
```

and let `D_6(U)` be `(RDF1)`. Each `z_j` is one fixed integral row on the
fixed regular `A8` packet. Its conjugation-module operator norm is unchanged
by amplification. Therefore there is a finite constant

```text
M_5=sup_(k>=1,U in U(20160k)) A(U)<infinity.           (RDP1)
```

If `atlas-six-relator-regular-face-defect-floor` holds with constant
`eta_6`, then

```text
A(U)<=M_5<=(M_5/eta_6)D_6(U).                         (RDP2)
```

This is `(FPL4)` with `C_5=M_5/eta_6`.

The converse explains why the scalar floor loses no qualitative content.
Assume `(FPL4)` with constant `C_5`. The established blow-up inequality
gives constants `D<infinity` such that

```text
sqrt(2)<=e_int(U)+D sqrt(A(U)).                        (RDP3)
```

Since `e_int(U)^2<=D_6(U)` and `A(U)<=C_5D_6(U)`, it follows that

```text
sqrt(2)<=(1+D sqrt(C_5))sqrt(D_6(U)),
D_6(U)>=2/(1+D sqrt(C_5))^2.                          (RDP4)
```

Thus `(FPL4)` implies `(RDF2)` as well. In particular the remaining direct
Atlas endpoint can be attacked without tracking four bridge displacements:
one uniform scalar separation of the six-relator regular matrix face is
already exactly enough.

