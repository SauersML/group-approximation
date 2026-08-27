---
rg: 2
id: fixed-finite-restriction-diagram-repair-proof
kind: route
title: Round the fixed branching-matrix kernel and polar-align the repaired restrictions
target: fixed-finite-restriction-diagrams-have-linear-hs-repair
requires:
  - finite-group-multiplicity-mismatch-pays-hs-energy
---

Let `Q=B/(ker phi_1 intersection ker phi_2)`, a fixed finite group, and
regard the two edge restrictions as representations `rho_i` of `Q`.  Write
`x_i` for the multiplicity vector of `pi_i` over `Irr(G_i)`, and let

```text
R_i:Z^(Irr(G_i))->Z^(Irr(Q))                          (FRP1)
```

be the fixed restriction matrix.  The weighted `L^1` discrepancy

```text
L=sum_(lambda in Irr(Q)) dim(lambda)
       |(R_1x_1-R_2x_2)_lambda|                       (FRP2)
```

is paid quadratically by `(FDR1)`.  Indeed
`finite-group-multiplicity-mismatch-pays-hs-energy`, applied to the identity
comparison and the fixed generating set, gives

```text
L/d <= C_0 epsilon^2.                                 (FRP3)
```

We use the following exact fixed-matrix integer error bound.  For fixed
nonnegative integer matrices `R_1,R_2` and fixed positive dimension rows,
there is `C_1` such that whenever nonnegative integer vectors `x_1,x_2`
have the same total dimension `d`, there are nonnegative integer vectors
`y_1,y_2`, **each still of total dimension exactly `d`**, with

```text
R_1y_1=R_2y_2,
sum_i sum_tau dim(tau)|x_i(tau)-y_i(tau)|
 <= C_1 ||R_1x_1-R_2x_2||_(1,dim).                   (FRP4)
```

Here is a direct proof with no dimension drift.  Let `H` be the fixed
integer matrix whose rows encode both `R_1z_1-R_2z_2=0` and the two
dimension equations, and put

```text
b_d=(0,d,d),                  Hx=b_d+e,                (FRP4a)
```

where the last two coordinates of `e` are zero.  Write
`e=e^+-e^-` coordinatewise and form the fixed slack-augmented matrix

```text
M=[H,-I,I].                                             (FRP4b)
```

The vector `z_0=(x,e^+,e^-)` is a nonnegative integer point of the fiber
`Mz=b_d`.  That fiber also contains `z_1=(y,0,0)`, where `y` consists of
`d` trivial vertex representations on both sides.  Conformally decompose
`z_1-z_0` into elements of the finite Graver basis of `M`.

Retain only the Graver summands having a nonzero coordinate in one of the
two slack blocks and add those summands to `z_0`.  Conformality has two
consequences.  First, every partial sum stays coordinatewise between
`z_0` and `z_1`, hence remains nonnegative.  Second, the retained summands
still take `(e^+,e^-)` exactly to `(0,0)`, because every omitted summand is
zero on both slack blocks.  The endpoint is therefore `(y',0,0)` with

```text
Hy'=b_d.                                                (FRP4c)
```

Thus the restrictions agree and both vertex dimensions are exactly `d`.
Each retained summand consumes at least one integer unit of the conformal
slack decrease, so, counted with multiplicity, there are at most
`||e||_1` of them.  If `G` is the maximum `L^1` norm of the vertex block of
an element of the fixed Graver basis, then

```text
||y'-x||_1<=G||e||_1.                                  (FRP4d)
```

Fixed positive dimension weights only change this constant.  This proves
`(FRP4)` uniformly in `d` and, crucially, preserves both dimension
equalities without adding or deleting dimensions.

Choose new exact vertex representations `pi_i^0` with multiplicity vectors
`y_i`, retaining the common old irreducible blocks and changing only the
complements.  Equations `(FRP3)--(FRP4)` imply that the changed physical
rank is at most `C_2 epsilon^2 d`; hence, for every group element,

```text
||pi_i(g)-pi_i^0(g)||_2<=2 sqrt(C_2) epsilon.          (FRP5)
```

The two restrictions of `pi_i^0` to `Q` now have identical multiplicity
vectors and are exactly unitarily equivalent.  Their identity comparison
still has edge defect `O_D(epsilon)`.  Project the identity onto their exact
intertwiner space and take its polar part.  The fixed finite-group
intertwiner gap bounds the displacement of that polar part; because the
multiplicity vectors agree, its kernel can be completed isotypically to a
full exact intertwining unitary `V` with

```text
||V-I||_2<=C_3 epsilon.                                (FRP6)
```

Set `pi~_1=pi_1^0` and `pi~_2=V pi_2^0 V^*`.  Then `(FDR2)` is exact, while
`(FRP5)--(FRP6)` give `(FDR3)`.
