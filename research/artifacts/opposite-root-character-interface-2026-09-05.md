# Opposite-root authentication: one depth is finite, two depths give the full core

The requested attack sought an opposite-root mechanism authenticating the
growing character-PVM interface while retaining the mark. The concrete
result is an exact algebraic boundary, recorded in
`weighted-leavitt-opposite-root-packets-have-finite-models` and
`weighted-leavitt-opposite-root-prefix-proof`.

A literal opposite root, complete native branch arms, and all aggregate
prefix actors at one depth still have finite marked models, including
every identity among those literal matrices. Coupling the first two depths
through that same opposite root generates the entire rank-three Leavitt
elementary group. This identifies the coefficient core which a successful
analytic decoder must use; it does not prove normalized-HS stability or
nonhyperlinearity.

## The weighted finite model

In `L=L_2(F_p)`, give `s_i` degree `1` and `t_i` degree `-1`.
For fixed row weights `a_i`, permit the `(i,j)` matrix coefficient to have
degree `a_i-a_j`. This weighted degree-zero ring is locally finite.

Indeed choose nonnegative depths `n_i=ell+a_i`, replace row `i` by its
`2^(n_i)` prefix coordinates, and send `X_ij` to the block

```text
(t_u X_ij s_v)_(|u|=n_i, |v|=n_j).
```

The prefix inverse and range-sum identities make this an exact ring
isomorphism onto a finite matrix algebra over `L_0`. Every new coefficient
has degree zero. Since `L_0` is the increasing union of the finite rings
`M_(2^N)(F_p)`, every finite inventory lies in a finite matrix ring.

This preserves the actual shared coefficients. Unlike the earlier typed
rectangular model, it does not represent different coefficient-`1`
occurrences by independently chosen auxiliary idempotents. All inverse,
range-sum, and mixed group identities among the selected matrices remain
literal identities.

At depth `r`, put `k=2^r` and use weights `(0,r,0)`. The packet

```text
X_u=x_12(t_u),        Y_u=x_23(s_u),        Z=x_31(1)
```

becomes the constant field-root packet on coordinates `1`, the `k`
prefixes `u`, and `3`:

```text
I+E_(1,u),           I+E_(u,3),           I+E_(3,1).
```

It generates exactly `SL_(k+2)(F_p)`. Both native reverse arms are
already present as `[Y_u,Z]=x_21(s_u)` and `[Z,X_u]=x_32(t_u)`.
The mark `[X_u,Y_u]=x_13(1)` survives.

For `c_g=sum_(u,v)g_(u,v)s_u t_v`, the aggregate actor
`D_g=diag(1,c_g^(-1),c_g)` becomes `diag(1,g^(-1),c_g)`.
Its third block is degree zero, although it is not scalar. One further
level-`r` core expansion places the full actor/root packet inside
`GL_(k(k+2))(F_p)`.

Only literal matrix identities are asserted. The indexed `D_g` family is
generally not a homomorphism in `g`, and its action on `Y_u` is not the
simple dual linear action. Also, a Whitehead expression for an aggregate
actor has separate root factors which may leave this weighted ring.
Additional relations involving those factors separately are additional
input, not consequences of the finite aggregate-actor model.

For an affine active corner, the branch operators must belong to `ARA`
and satisfy the Leavitt relations with unit `A!=0`. Map the abstract ring
into that corner and extend its units by the identity on `1-A`. The
fixed-weight packet's elementary image remains locally finite and
`x_13(A)` remains nonidentity.
No local-finiteness assertion is made about the whole Steinberg preimage.

## Two depths recover the entire coefficient core

At depths one and two retain the same `Z=x_31(1)` and use

```text
X_i=x_12(t_i),             Y_i=x_23(s_i),
X_(ij)=x_12(t_j t_i),      Y_(ij)=x_23(s_i s_j).
```

Then

```text
[X_i,Y_(ij)]=x_13(s_j),
[X_(ij),Y_i]=x_13(t_j).
```

The same root position now contains coefficients of degrees `0,1,-1`,
so no fixed row weights can contain the packet. This failure has a precise
group-theoretic consequence. The constant `(1,3)` Weyl gives
`x_31(t_i)`, while `[Z,X_i]=x_32(t_i)`. Therefore

```text
[x_13(s_i),x_32(t_i)]=x_12(s_i t_i),
[Y_i,x_31(t_i)]=x_21(s_i t_i).
```

The Leavitt range sum gives `x_12(1)` and `x_21(1)`. Constant Weyl
permutations now move the raw `s_i,t_i` coefficients to every root
position; spare-index commutators multiply coefficients and root addition
adds them. The displayed finite generating packet consequently generates
exactly `EL_3(L_2(F_p))`.

Both the weighted-ring argument and this generation argument were checked
independently by the `audit_induction` agent, including prefix order,
opposite-root signs, and the nonhomomorphic aggregate-actor caveat. No
computation or local code execution was used.

## Consequence for the requested PVM mechanism

A fixed-depth opposite packet cannot collapse the mark: its finite regular
model has zero relation defect and marked squared HS distance two. It also
has canonical trace on every nonidentity element of its root packet.
Merely adjoining the opposite of the central mark to the prefix actors
therefore does not authenticate a supercritical growing root table.

The two-depth packet escapes that finite model, but is already the full
rank-three coefficient core. Its exact generation identities do not give
a uniform estimate exposing a matrix-size-dependent root table and its
full actor-covariance energy. That analytic estimate remains the actual
open step. The new result narrows its required input to the crossed-depth
raw coefficients; a degree-balanced opposite packet and the existence of
the generation identity alone are insufficient.
