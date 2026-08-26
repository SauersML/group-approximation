---
rg: 2
id: endpoint-whitehead-star-braid-proof
kind: route
title: Compute the endpoint star Coxeter rows and the invariant missing-sign line
target: endpoint-whitehead-star-braid-synchronizes-native-gauges
requires:
  - native-j1-extension-gives-gl5-but-only-second-whitehead-gram
  - native-whitehead-hecke-head-has-order-seven-anchor
  - endpoint-odd-actor-retains-native-factor-gauge
---

On the block `D_5` of the target claim, the standard partial-Whitehead
matrix is the characteristic-two transposition of its two equivalent
projective summands.  The native orientations therefore give exactly

```text
J_1=(u_1 u_2),       J_2=(u_2 u_3),       W=(u_2 u_4). (1)
```

Two distinct transpositions in `(1)` share exactly `u_2`; their product is
a three-cycle.  This proves all rows `(EWS2)--(EWS3)` on `D_5`.  Every word
is the identity on `1-D_5`, so the same identities hold globally in the
elementary group.

On a common homogeneous Pauli block, cancel the fixed label factors in
the braid rows.  This gives

```text
V_i V_j V_i=V_j V_i V_j.                              (2)
```

The factors are involutions.  Hence

```text
V_j=(V_iV_j)V_i(V_iV_j)^(-1),                         (3)
```

which proves `(EWS5)`.  For a central involution `D`, direct collection
instead gives

```text
((J_1D)W)^3=(J_1W)^3D^3=D,                           (4)
```

proving `(EWS7)`.  Notice that `(4)` has odd incidence in `J_1`; it is
precisely the ordinary occurrence row absent from the earlier `W,M`
factorization interface.

It remains to justify the sharp support fence.  Write the active
five-dimensional projective space in the ordered basis
`(u_0,u_1,u_2,u_3,u_4)`.  The nontrivial incidences of the signed source
inside this block are

```text
C_2 : external -> u_0,
C_3 : u_0 -> external,
v   : u_1 -> u_0,
w   : u_1 -> external,
s   : u_2 -> external.                               (5)
```

The root `C_1` is supported on the `q`-part of coordinate `2`, orthogonal
to the active `e_3` summand there, and is fixed by the whole actor.

Let `g` normalize the root group in `(5)` and preserve its signed
character.  The unique active target of the first row forces
`g u_0=u_0`.  The unique active-target row `v` then forces the pulled-back
covector `u_1^*g^(-1)=u_1^*`.  The three external-target rows force

```text
span(u_0^*,u_1^*,u_2^*)g^(-1)
   =span(u_0^*,u_1^*,u_2^*).                          (6)
```

Because `g^(-1)u_0=u_0`, the coefficient of `u_0^*` in
`u_2^*g^(-1)` is zero.  Equations `(5)--(6)` and invertibility then give

```text
u_2^*g^(-1)=u_2^*+epsilon u_1^*.                     (7)
```

The root `r=x_58(a_2)` is the rank-one map `u_2 -> u_0`.  Conjugating it
using `g u_0=u_0` and `(7)` gives

```text
g r g^(-1)=r v^epsilon.                              (8)
```

All these row roots commute, so `(8)` is literal root multiplication, not
an equality only after passing to a quotient.  The prescribed character
has `lambda_2(v)=+1`; hence `r` and `rv` have the same sign on `p_2`.
This proves `(EWS9)` and the support conclusion.

For the stronger moving-packet model, the six roots in `(EWS11)` commute:
the first triple has common active target `u_0`, the second triple has
common external target, and the cross incidences are nonopposite.
Conjugation by `J_1=(u_1u_2)` and `W=(u_2u_4)` gives the two simultaneous
coordinate transpositions stated in the claim.  Hence
`A semidirect S_3` is an exact quotient of this displayed covariance table.

In its character-orbit representation, the character `(EWS12)` has orbit
size three.  The signed `p_2` conditions require `v=w=s=+1`, so only the
orbit point whose unique positive entry in `(v,r,r')` is at `v` survives.
The word `W` exchanges `r,r'`, both negative, and fixes that point.  The
word `J_1` exchanges `v,r` and moves it to an orthogonal character atom.
This gives `(EWS13)` directly.

The proof deliberately separates two statements.  The star braid is a
global elementary-group relation and genuinely synchronizes reservoir
gauges.  The stabilizer profile and the finite `A semidirect S_3` model are
scoped exact representations of the indicated return/moving-root tables,
and are used solely to show why those tables cannot imply positive `q_1`
mass.
