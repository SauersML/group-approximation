---
rg: 2
id: two-sided-stinespring-controls-closing-face
kind: route
title: Pair both Stinespring off-corners and accumulate only linear word error
target: scalar-tree-perturbations-linearly-control-closing-face
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
left side of `(3)`.  The previous square-root estimate stopped here.  The
closing word supplies a second small off-corner.  For `g in P_13`, choose a
shortest expression

```text
g=p_1...p_l,       p_j in P_1 union P_3,       l<=R_13.
```

Write `u_j=u_(p_j)` and `x=u_2...u_l`.  Then

```text
||(1-P)pi(x)V||
 <=||pi(x)V-V||
 <=sum_(j=2)^l ||(pi(u_j)-1)V||
 <=(l-1)sqrt(2eta).                                       (4)
```

The last inequality follows from

```text
||(pi(u_j)-1)V||^2
 =||2-theta(u_j)-theta(u_j)^*||<=2eta.
```

Pairing the two off-corners in `(2)` therefore gives

```text
||theta(u_1x)-theta(u_1)theta(x)||<=2(l-1)eta.             (5)
```

Iterating `(5)` from the left yields

```text
||theta(u_1...u_l)-theta(u_1)...theta(u_l)||
 <=2eta sum_(k=1)^(l-1)k=l(l-1)eta.                       (6)
```

The product of the contractions `theta(u_j)` is within `l eta` of `1` by
telescoping.  Consequently

```text
||theta(u_g)-1||<=l^2 eta<=R_13^2 eta.                    (7)
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

so `||A_g||<=||X||`.  Applying `(7)` entrywise therefore yields

```text
||(id_(M_m) tensor (theta-E_epsilon^D))(X)||
 <=sum_g ||A_g|| ||theta(u_g)-1||
 <=d_13 R_13^2 eta ||X||.                                 (8)
```

Taking the supremum over `m` proves `(STQ3)`, and `(STQ4)` follows by
rearranging it.  No smallness assumption on `eta` is needed.

The proof is uniform in the codomain.  When `D` is finite-dimensional, ucp
maps from the fixed finite-dimensional operator system are represented by
their finite Choi matrices, so the same inequality applies directly to the
finite feasibility problem `(STQ5)`.
