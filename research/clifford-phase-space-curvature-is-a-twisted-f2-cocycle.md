---
rg: 2
id: clifford-phase-space-curvature-is-a-twisted-f2-cocycle
kind: claim
title: Fixed-action Clifford phase-space curvature is a twisted F2 two-cocycle
distinct_from:
  finite-clifford-symplectic-section-obstruction: that says the full Clifford extension does not split over the entire finite symplectic group; this identifies the exact finite linear obstruction after one coefficient space and one partial symplectic action have already been fixed
  minimal-marked-graph-finite-window-phase-space-section: that asks for a completion and lifts with zero Pauli curvature; this proves that the lift-selection part of that target is a finite twisted-coboundary problem but does not choose the completion or symplectic extensions
  private-neighbour-density: that counts Laurent parameters avoiding finitely many affine denominator cosets; this is linear algebra over one already fixed binary symplectic coefficient module
---

Let `K` be a finite nondegenerate binary symplectic space with form `b`, and
choose Weyl operators normalized by

```text
W(v) W(w) = (-1)^c(v,w) W(v+w),
c(v,w) + c(w,v) = b(v,w).
```

Let `E` be a finite actor table.  Suppose symplectic maps `S_g in Sp(K)`
have already been chosen and satisfy

```text
S_g S_h = S_(gh)
```

on every tested multiplication triangle.  Choose Clifford lifts `U_g` and
write

```text
U_g W(v) U_g^* = (-1)^ell_g(v) W(S_g v),
U_g U_h U_(gh)^* = lambda(g,h) W(a(g,h)).             (CPC1)
```

Then the Pauli labels `a(g,h) in K` obey the twisted cocycle equation

```text
a(g,h) + a(gh,k) = S_g a(h,k) + a(g,hk)              (CPC2)
```

on every tested associativity tetrahedron.  They are determined by the
conjugation phases through

```text
b(a(g,h), S_(gh)v)
 = ell_h(v) + ell_g(S_h v) + ell_(gh)(v).             (CPC3)
```

Changing lifts by `U'_g = W(r_g) U_g` changes the labels by

```text
a'(g,h) = a(g,h) + r_g + S_g r_h + r_(gh).            (CPC4)
```

Consequently, for fixed `K` and fixed `S`, scalar-only curvature on the
tested table is equivalent to the finite `F_2`-linear system

```text
delta_S r = a.
```

Equivalently, the sole lift obstruction is the restricted class
`[a] in H^2(table; K_S)`: it vanishes exactly when every left-nullspace
functional for the matrix of `delta_S` annihilates `a`.  In particular, on
a multiplication table whose actor two-complex has no two-cycle obstruction
(for example, a recursively attached tree of multiplication triangles), the
lifts can always be repaired to have scalar curvature.

## Scope

The claim begins only after the finite symplectic coefficient space and all
actor maps have been fixed.  It does not say that the private-neighbour
completion parameters enter `a` affinely, and it does not trivialize the
global class from `finite-clifford-symplectic-section-obstruction`.
