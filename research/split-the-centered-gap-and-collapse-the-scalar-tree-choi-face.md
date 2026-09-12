---
rg: 2
id: split-the-centered-gap-and-collapse-the-scalar-tree-choi-face
kind: route
title: Split the centered gap and use multiplicative domains to collapse scalar tree restrictions
target: centered-gap-is-on-a-tree-or-forces-tree-motion
requires:
  - global-triangle-separator-survives-mod-augmentation
---

Equation `(MAS2)` and the bounded face decomposition give `(CGT2)`.  If
either tree summand is at least `delta/6`, then `(CGT3)` holds.  Otherwise

```text
c_12+c_23<delta/3,
```

so `(CGT2)` gives `c_13>2delta/3`, and hence the weak inequality `(CGT4)`.
The first branch is the face-specific version of the Choi positivization and
trivial-summand deletion already proved in
`global-triangle-separator-survives-mod-augmentation`.

For the second branch, take `Phi in F_scalar`.  On the shared face
`C^*(P_1)=C^*(P_12) intersect C^*(P_13)`, its closing restriction satisfies

```text
Phi(u_p)=1_A       for every p in P_1.                    (1)
```

The same argument on `P_3` gives `(1)` for every `p in P_3`.  The restriction

```text
Phi_13=Phi|_(C^*(P_13))
```

is ucp.  A unitary in the domain of a ucp map whose image is unitary belongs
to the multiplicative domain.  Hence every `u_p`, `p in P_1 union P_3`, lies
in the multiplicative domain of `Phi_13`.  The two standard rank-one
subgroups `P_1` and `P_3` generate the rank-two parabolic `P_13`.  Therefore
the multiplicative domain is all of `C^*(P_13)`, and

```text
Phi_13(u_g)=1_A=epsilon(u_g)1_A       for every g in P_13. (2)
```

Together with the two defining scalar tree restrictions, `(2)` shows that
`Phi=E_epsilon^A` on the vector-space sum `S_Delta`, proving `(CGT6)`.

This also explains the Boca failure exactly.  The two scalar tree maps glue
over `P_2`, but any closing map compatible with them is scalar on both edge
groups `P_1,P_3`; multiplicative-domain rigidity then makes it scalar on the
whole closing face.  The explicit non-scalar `P_13` section cannot be inserted
without moving at least one tree restriction.
