---
rg: 2
id: atlas-reference-packet-root-ellipse-countermodel-proof
kind: route
title: Compute the four regular traces from the coordinate three-cycle
target: atlas-reference-packet-root-ellipse-countermodel
requires:
  - atlas-a4-packet-centralizer-product-compiler
  - atlas-a8-minimal-four-transvection-cycle
---

The exact reference-alignment audit verifies that `r_0` satisfies all thirty
packet pair-cubes.  Applying the left regular representation and then tensoring
with `I_k` preserves these identities and gives exact regular chart type.

On the standard basis of `F_2^4`, the displayed matrix acts by the coordinate
permutation

```text
p: 0 |-> 2,  1 |-> 1,  2 |-> 3,  3 |-> 0.
```

For a transvection `t_ij=I+E_ij`, conjugation therefore gives

```text
r_0 t_ij r_0^-1 = t_(p(i),p(j)).                      (1)
```

For the minimal cycle `T={t01,t12,t23,t30}`, equation `(1)` gives respectively

```text
t21, t13, t30, t02.
```

None equals its original transvection.  Hence each group element

```text
r_0 t_ij r_0^-1 t_ij^-1
```

is nonidentity.  The normalized trace of a nonidentity element in `Reg(A8)`
is zero, and tensor amplification does not change normalized trace.  By the
definition

```text
x_ij(U_k)^2
 =1-Re tau(U_k rho_k(t_ij)U_k^*rho_k(t_ij)^*)
```

all four squared root deficits are exactly one.  Thus every `x_ij=1`, and
direct substitution gives `S=8` and the value `64+8+1=73` in
`(A4-REF-ELLIPSE)`.
