---
rg: 2
id: stw83-commuting-cone-two-colour-firewall
kind: claim
title: Commuting cone cutters and block-diagonal plateau maps cannot supply the missing two colours
distinct_from:
  stw83-plateau-buffer-recolouring-hinge: that gives a sufficient plateau condition and rules out a block-diagonal whole-corner implementation; this adds the independent cone-dimension obstruction to every uniformly local commuting scalar-functional-calculus implementation.
  stw83-circle-unitary-order-zero-plus-constants-gap: that is a rank-one winding-number obstruction for one order-zero star plus constants; this is a global support-colouring obstruction over the full phase/cutoff cone.
---

Put

```text
X=Cone(T)=({0} union (0,1] times T),
```

where all points `(0,z)` are identified, and identify `X` with the
closed disk by `(r,z) |-> rz`.  A two-label scalar cutter of mesh
`epsilon` is a finite family

```text
g_(i,j) in C(X)_+,                    i in {0,1},
```

such that

```text
g_(i,j) g_(i,k)=0                     (j!=k),
norm(1-sum_(i,j) g_(i,j))<1/4,
diam(coz(g_(i,j)))<epsilon.
```

There is an `epsilon_0>0` for which no such cutter exists.  In
particular, there is no arbitrarily fine two-colour recolouring whose
supports are commuting scalar functions of the coefficient phase and a
continuous Toeplitz cutoff.  Any universal local functional-calculus
scheme of that form would give the forbidden cutters on the joint
phase/cutoff cone.

There is a second endpoint obstruction.  Let `D=M_r(C(T))`, let
`0<p<1` be a constant projection, and put `q=1-p`.  There is no net
of two-colour approximations of `id_D` for which the first outgoing
range is contained in `pDp` and the second outgoing range commutes
with `p`.

Applied to

```text
A_N=C*(S^N tensor 1, K tensor C(T)),
```

these two statements rule out both of the following proposed repairs of
the coefficient-valued Brake--Winter construction:

1. fill the transition by a uniformly local scalar partition in the two
   commuting variables `(cutoff, coefficient phase)`;
2. keep the second inner colour block diagonal across the plateau
   boundary.

They do not rule out the remaining buffer escape.  A successful
two-colour construction may extinguish all coefficient variation before
the scalar transition, and then use stage-dependent, genuinely
noncommuting matrix supports across a long buffer.  No
nuclear-dimension value for `A_N` is inferred here.
