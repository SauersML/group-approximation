---
rg: 2
id: native-whitehead-hecke-order-seven-proof
kind: route
title: Compute the native Whitehead--Hecke packet on three equivalent prefix corners
target: native-whitehead-hecke-head-has-order-seven-anchor
requires:
  - native-whitehead-corner-collapses-hecke-flags
  - center-chain-mixed-hecke-polars-share-a1-tail
---

We prove both rows at once.  Fix `m=1,2` and abbreviate

```text
a=a_m=s_1t_(0^m),              b=b_(m+1)=s_(0^(m+1))t_1,
x=ba=s_(0^(m+1))t_(0^m),      y=s_(0^m)t_(0^(m+1)).   (1)
```

Prefix cancellation gives

```text
yx=e_(0^m)=:e,        xy=e_(0^(m+1))=:f.               (2)
```

Also, with `q=s_1t_1`,

```text
qa=a=ae,              fb=b=bq.                         (3)
```

Use the three matrix indices

```text
(k,j,i)=(4,7,8) for m=1,       (k,j,i)=(5,8,9) for m=2
```

and put

```text
A=x_kj(a),              B=x_ik(b),
J=x_ij(x)x_ji(y)x_ij(x).                               (4)
```

Equations `(2)--(3)` show that the projection

```text
D=qE_kk+eE_jj+fE_ii                                      (5)
```

reduces `A,B,J`, and all three operators are the identity on `1-D`.
The maps `a:eR -> qR`, `b:qR -> fR`, and `x:eR -> fR` identify the three
summands in `(5)`.  In the ordered coordinates `(qR,eR,fR)`, direct
multiplication gives

```text
A=[[1,1,0],             B=[[1,0,0],
   [0,1,0],                [0,1,0],
   [0,0,1]],               [1,0,1]],

J=[[1,0,0],
   [0,0,1],
   [0,1,0]].                                             (6)
```

The last matrix is exactly the characteristic-two Whitehead block

```text
[[1-f,x],[y,1-e]]
```

on the ordered indices `(i,j)`, transported through the identifications in
`(5)`.  Thus no abstract completion or auxiliary projection has been
inserted.

Let `M=JBA`.  Over `F_2`, `(6)` gives

```text
M=[[1,1,0],
   [1,1,1],
   [0,1,0]],

M^3+M+I=0.                                               (7)
```

Multiplying `(7)` by `M`, and then substituting `(7)` repeatedly, gives
`M^7=I`.  Equivalently, `X^3+X+1` is a factor of `X^7+1` over `F_2`.
Since `M` has order seven, while the transvections `A,B` and the swap `J`
generate all elementary moves among the three summands, the packet is the
faithful natural `GL_3(F_2)` packet.  Because the three words are the
identity on `1-D`, `(JBA)^7=1` holds in the full elementary matrix group.

For `m=1`, `(A,B,J)=(A_1,B_2,J_1)`, so `(J_1B_2A_1)^7=1`.
For `m=2`, `(A,B,J)=(A_2,B_3,J_2)`, so `(J_2B_3A_2)^7=1`.
The mixed polar notation has `u_1=B_2A_1` and
`u_2=B_3A_2A_1`; since `A_1^2=1`, the latter equality is equivalently
`B_3A_2=u_2A_1`.  This proves `(OWH3)--(OWH4)`.

Finally, if `D` commutes with the packet and `D^2=1`, then it commutes with
`J_i v_i` and `D^7=D`.  Therefore

```text
((J_iD)v_i)^7=(J_iv_i)^7D^7=D,
(J_i(v_iD))^7=(J_iv_i)^7D^7=D.                         (8)
```

Taking the operator norm after subtracting the identity gives `(OWH6)`.
This proves the exact elementary-group spectator-gauge coercivity and
completes the claim.  Notice that the calculation proves equality after the
canonical map `St_20(R)->EL_20(R)`.  It does not identify the possible
central-kernel value of the same written word upstairs; that explicitly
recorded lift check is separate from the block calculation.
