---
rg: 2
id: leavitt-composite-omega-abstract-fence-does-not-lift-proof
kind: route
title: Test the universal-gate retraction against the first exact Leavitt packet relations
target: leavitt-composite-omega-abstract-fence-does-not-lift
requires:
  - leavitt-degree-four-affine-omega-candidate
  - leavitt-omega-has-an-explicit-distorted-target
---

The composite-involution refinement replaces the source and target pairs by

```text
b=r^2 a r^(-2),      d=p^2 c p^(-2),
[a,b]=1,             [c,d]=x_15(s_0^2) !=1.          (CL1)
```

All four entries are involutions.  The natural degree-four slots are

```text
(r,e,a,c,1,b,d,p),          signs ++-++-++,           (CL2)
```

so the two nonlinear orbit relators conjugate the source gates `a_0,b_0`.

There is a universal-gate countermodel to the hoped-for four-cell transport.
It uses a group containing `K=C_2*C_20=<C,P>`, retains
`[C,P^2CP^(-2)] !=1`, and satisfies the four orbit relators together with
the formal relations in `(CL1)`.  Thus no picture using only those displayed
laws can have outer boundary `[c_0,d_0]`.

That countermodel does **not** lift to the actual packet subgroup.  Two short
failures occur before any appeal to simplicity.

First, it sets `r_0=1` while retaining `p_0=P` of order 20.  The actual
packet identities

```text
r=qp,       q^2=1                                    (CL3)
```

would give `q_0=P^(-1)` and hence `P^2=1`, a contradiction.

Second, the model assigns `c_0=C` and `e_0=CSC`, where `C,S` are distinct
involutions.  In the actual elementary group

```text
[e,c]=[x_12(t_1),x_13(s_0)]=1                       (CL4)
```

because the roots have the same row.  In the countermodel,

```text
[C,SCS]=(SC)^2 !=1.                                  (CL5)
```

Consequently the abstract four-cell fence proves only that the relations
`(CL1)` are insufficient.  A genuine fence must realize every coefficient
copy as a full copy of the Leavitt group (or at least respect `(CL3)--(CL4)`
and the remaining packet relations).  Conversely, `(CL3)--(CL4)` do not by
themselves prove the desired kill; whether they repair the transport remains
open.
