---
rg: 2
id: finite-word-stinespring-controls-closing-face
kind: route
title: Accumulate the Stinespring defect along a shortest closing-face word
target: scalar-tree-perturbations-force-square-root-closing-control
requires: []
---

Let `theta=Phi|_(B_13)` and abbreviate `eta=eta(Phi)`.  Compatibility on the
overlaps of the three concrete face algebras gives

```text
||theta(u_p)-1||<=eta             (p in P_1 union P_3).    (1)
```

Write a Stinespring representation as

```text
theta(x)=V^* pi(x)V,       P=VV^*.
```

If `u` is one of the unitaries in `(1)` and `x` is a contraction, then

```text
theta(ux)-theta(u)theta(x)=V^*pi(u)(1-P)pi(x)V.            (2)
```

Since `theta(u)` is a contraction and is within `eta` of `1`,

```text
||1-theta(u)theta(u)^*||
 <=||1-theta(u)||+||theta(u)(1-theta(u)^*)||
 <=2eta.                                                   (3)
```

The square of the norm of the left off-corner in `(2)` is bounded by the
left side of `(3)`.  Hence

```text
||theta(ux)-theta(u)theta(x)||<=sqrt(2eta).                (4)
```

For `g in P_13`, choose a shortest expression

```text
g=p_1...p_l,       p_j in P_1 union P_3,       l<=R_13.
```

Iterating `(4)` from the left, and then telescoping the product of the
`theta(u_(p_j))` against `1`, gives

```text
||theta(u_g)-1||
 <=(l-1)sqrt(2eta)+l eta
 <=(R_13-1)sqrt(2eta)+R_13 eta.                            (5)
```

It remains only to pass from the Fourier basis to cb norm; no compactness is
needed.  For every matrix size `m`, write uniquely

```text
X=sum_(g in P_13) A_g tensor u_g in M_m(C^*(P_13)).
```

With `tau` the canonical normalized trace,

```text
A_g=(id tensor tau)(X(1 tensor u_g^*)),
```

so `||A_g||<=||X||`.  Applying `(5)` entrywise therefore yields

```text
||(id_(M_m) tensor (theta-E_epsilon^D))(X)||
 <=sum_g ||A_g|| ||theta(u_g)-1||
 <=d_13((R_13-1)sqrt(2eta)+R_13 eta)||X||.                 (6)
```

Taking the supremum over `m` proves the first inequality in `(STQ3)`; for
`eta<=1`, the second follows from `eta<=sqrt(eta)`.  If `eta>1`, `(STQ4)` is
automatic, while if `eta<=1`, it follows by rearranging `(STQ3)`.

The proof is uniform in the codomain.  When `D` is finite-dimensional, ucp
maps from the fixed finite-dimensional operator system are represented by
their finite Choi matrices, so the same inequality applies directly to the
finite feasibility problem `(STQ5)`.
