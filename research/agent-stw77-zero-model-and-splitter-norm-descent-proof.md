---
rg: 2
id: agent-stw77-zero-model-and-splitter-norm-descent-proof
kind: route
title: Apply Christensen and repair transported corner rows
target: agent-stw77-zero-model-and-splitter-norm-descent
requires:
  - agent-stw77-zero-near-witnesses-descend-properness
  - stw77-proper-support-models-force-oinfty-stability
---

We use Christensen's finite-dimensional one-sided perturbation theorem in
the quantitative form recorded as Theorem 2.14 of Jaime--Willett,
[*Complexity rank for C-star algebras*](https://arxiv.org/abs/2205.04704).
Under `(1)` it gives a partial isometry `v` with

```text
v^*v=1,
vEv^* subset C,
||v-1||<120 sqrt(epsilon).                             (5)
```

The last bound is less than one, so `v` is invertible.  An invertible
isometry is unitary.  This proves `(3)`.

Put

```text
p_j=v e_j v^*,
t_(j,k)=v s_(j,k)v^*.
```

The `p_j` are minimal projections of `E_0=vEv^*`, and the `t_(j,k)` are
exact orthogonal splitting isometries in `p_jB(H)p_j`.  Moreover

```text
dist(t_(j,k),C)
 <= dist(s_(j,k),C)+||v s_(j,k)v^*-s_(j,k)||
 < delta+2||v-1||
 < delta+240 sqrt(epsilon)
 <1/4.                                                 (6)
```

Apply `agent-stw77-zero-near-witnesses-descend-properness` to the faithful
identity representation of `C`, with support `p_j` and splitters
`t_(j,1),t_(j,2)`.  It follows that every `p_j` is properly infinite in
`C`.  Matrix units in each summand transport this conclusion to every
minimal projection of `E_0`.

For the approximation estimate, if `||x_l-c_l||<eta` and both are
contractions, then

```text
||v x_l v^*-c_l||
 <=||v x_l v^*-x_l||+||x_l-c_l||
 <2||v-1||+eta
 <eta+240 sqrt(epsilon),
```

which is `(4)`.

Finally suppose the two defects can be made arbitrarily small for the
absorbed models of a nuclear-dimension-zero map.  Given a finite image packet
and a target tolerance, first make `eta` and `epsilon` small enough that
`(4)` is below that tolerance, and impose `(2)`.  The resulting `E_0 subset
C` is a one-sided finite-dimensional model with properly infinite minimal
supports.  Pull it back through the faithful representation and apply
`stw77-proper-support-models-force-oinfty-stability`.

The two obstruction nodes show both hypotheses are essential for this
argument.  Generated finite-packet models need not satisfy `(1)`, and even
the exact inclusion `E subset C` does not suffice without `(2)`.
