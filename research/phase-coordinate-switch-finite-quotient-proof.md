---
rg: 2
id: phase-coordinate-switch-finite-quotient-proof
kind: route
title: Use the same finite support quotient in both faithful coordinates
target: phase-coordinate-switch-hnn-is-residually-finite
requires: []
---

Let `w` be Britton reduced in `(PCS2)` and contain a stable letter.  Write an
intervening base syllable as `(x,y,p)`.  Its two associated-subgroup tests are

```text
(x,y,p) in G_0 iff y=1 and p=Theta_0(x),
(x,y,p) in G_1 iff x=1 and p=Theta_1(y).                (PCS3)
```

Choose one finite quotient `q_P:P->F` preserving every nonidentity phase
difference `p Theta_0(x)^(-1)` or `p Theta_1(y)^(-1)` which occurs in a
forbidden pinch with the other faithful coordinate equal to `1`.  Residual
finiteness of `A` similarly gives a finite-index normal subgroup `N_sep`
avoiding every nonidentity `x` or `y` which itself certifies a forbidden
pinch.  Put

```text
N=N_sep intersect ker(q_P Theta_0) intersect ker(q_P Theta_1),
A_bar=A/N.                                               (PCS4)
```

Then `A_bar` is finite, both phase maps descend to `A_bar`, and using the same
quotient in the two copies of `A` gives a finite base quotient

```text
B -> A_bar times A_bar times F.
```

Every test in `(PCS3)` survives.  Hence `w` maps to a Britton-reduced,
nontrivial word in an HNN extension of a finite group along finite subgroups.
That target is virtually free and residually finite, so a further finite
quotient separates `w`.

For a nontrivial base word `(x,y,p)`, choose the separating quotients in
`(PCS4)` to preserve one nonidentity coordinate.  Both phase maps still
descend, and the base word survives.  Therefore every nonidentity element of
`E` is detected in a finite quotient.
