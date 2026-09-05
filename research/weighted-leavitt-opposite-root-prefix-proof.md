---
rg: 2
id: weighted-leavitt-opposite-root-prefix-proof
kind: route
title: Expand differently weighted rows into prefix coordinates over the finite Leavitt core
target: weighted-leavitt-opposite-root-packets-have-finite-models
requires: []
---

The degree-zero algebra `L_0` is the increasing union of finite matrix
rings. At level `N`, its matrix units are `s_u t_v` for `|u|=|v|=N`;
the relation `s_u t_v=sum_i s_(ui)t_(vi)` embeds one level into the next.
Every homogeneous degree-zero element belongs to some level, by the
Leavitt relations and the normal form consisting of sums of `s_u t_v`.

Choose an integer `ell` such that `n_i=ell+a_i>=0`, and put
`D=sum_i 2^(n_i)`. Form rectangular matrices

```text
T_((i,u),j)=delta_(i,j)t_u,       |u|=n_i,
S_(i,(j,v))=delta_(i,j)s_v,       |v|=n_j.
```

The prefix inverse and range-sum identities give `TS=I_D`, `ST=I_m`.
Thus `Phi(X)=TXS` is a ring isomorphism onto its image, with inverse
`Y -> SYT`. For `X in B(a)`, each image entry has degree

```text
deg(t_u X_ij s_v)=-n_i+(a_i-a_j)+n_j=0.
```

Conversely, `SYT` has its `(i,j)` entry in degree `n_i-n_j=a_i-a_j`
when `Y` has degree-zero entries. Hence

```text
B(a) ~= M_D(L_0).                                      (WOP3)
```

Every finite inventory on the right belongs to one finite matrix ring.
For a finite group-generator inventory include its inverses too; their
images are units of that same finite ring. This proves local finiteness of
the unit group without any analytic or representation-theoretic input.

For weights `(0,r,0)`, take `ell=0`, so `D=k+2`. Label the new coordinates
by `1`, the `k` prefixes `u`, and `3`. The three families become

```text
Phi(X_u)=I+E_(1,u),
Phi(Y_u)=I+E_(u,3),
Phi(Z)=I+E_(3,1).
```

The directed graph `1 -> u -> 3 -> 1` is strongly connected. Repeated
elementary commutators along simple paths produce every elementary matrix
over `F_p`; powers supply its scalar coefficients. Thus these generators
give exactly `SL_(k+2)(F_p)`. The reverse native arms are already present:
`[Y_u,Z]=x_21(s_u)` and `[Z,X_u]=x_32(t_u)`.

For an actor, the same map gives

```text
Phi(D_g)=diag(1,g^(-1),c_g).
```

Its entries belong to the level-`r` finite core `M_k(F_p)`. So all actors,
native arms, and opposite roots together lie in
`GL_(k(k+2))(F_p)` after that core expansion. No multiplication law for
the indexed actor family is used.

The image of `w=x_13(1)` is a nontrivial elementary matrix. A regular
representation of the resulting finite group therefore has trace zero on
`w` and squared normalized HS distance two from the identity.

For an active corner, the assignment `1 -> A`, with all branch operators
in `ARA`, gives a homomorphism from the abstract Leavitt algebra to that
corner. Extend its matrix-unit action by the identity on `1-A`. An image of
the locally finite unit group is locally finite, and `I+AE_13!=I` since
`A!=0`. This proves the marked conclusion without asserting faithfulness
or local finiteness for the full ambient Steinberg group.

For `(WOP4)`, write the depth-one generators as `X_i,Y_i`, the depth-two
generators as `X_(ij),Y_(ij)`, and `Z=x_31(1)`. The prefix convention gives

```text
[X_i,Y_i]=x_13(1),
[X_i,Y_(ij)]=x_13(s_j),
[X_(ij),Y_i]=x_13(t_j).                                 (WOP5)
```

The constant opposite pair `x_13(1),Z` supplies the `(1,3)` Weyl word,
so `x_31(t_i)` is available up to a sign corrected by inversion.
Also `[Z,X_i]=x_32(t_i)`. Therefore

```text
[x_13(s_i),x_32(t_i)]=x_12(s_i t_i),
[Y_i,x_31(t_i)]=x_21(s_i t_i).
```

Root additivity and `s_0t_0+s_1t_1=1` give both `x_12(1)` and
`x_21(1)`. Together with the constant `(1,3)` pair these generate the
constant `SL_3(F_p)`, including its Weyl permutations. Conjugating the raw
`s_i,t_i` roots in `(WOP5)` now supplies them in every root position.
Finally, root additivity and

```text
[x_ab(u),x_bc(v)]=x_ac(uv)             for distinct a,b,c
```

inductively supply every polynomial coefficient in every root position.
These are all elementary generators of `EL_3(L_2(F_p))`, proving `(WOP4)`.
