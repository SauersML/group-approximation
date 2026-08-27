---
rg: 2
id: atlas-t30-is-one-parabolic-c3-bridge
kind: claim
title: The transverse t30 opcode is one central-C3 reflection conjugated through the affine parabolic
artifacts:
  - experiments/atlas_t30_parabolic_c3_bridge.py
  - experiments/atlas-t30-parabolic-c3-bridge.json
distinct_from:
  atlas-a4-19243-parabolic-subgroup-ladder: that proves the subgroup ladder P below A8; this identifies the exact shortest bridge from the packet C3 sector across P to the particular transverse opcode t30 and records its quantitative covariance consequence.
---

Use the exact `GL_4(F2)` coordinates of
`atlas-a4-19243-parabolic-subgroup-ladder`.  Let `b` be the repeated
first-chart involution of collision `19243`, let `z` be the following
nonidentity element of `Z(H_18) ~= C3`, and choose one letter from each of the
two packet `S3` factors:

```text
h = h6_2 = 01000000000101000001000000000001,
k = k_0  = 01010000010000000000010000000001,
b        = 01000000000100000000010100000001,
z        = 01000000000100000000010100000100.
```

Put `c=hk`.  Then exact multiplication over `F2` gives

```text
t30 = c^-1 z b c.                                      (T30-PC3-1)
```

Thus the unique four-cycle direction leaving the affine parabolic is a
conjugate of the reflection `zb` in the packet cell

```text
<z,b> ~= S3.
```

This factorization has the following dimension-free normalized-Hilbert--
Schmidt consequence.  For any unitary representation `rho` and any relative
unitary `U`, put

```text
delta_U(g)=||U rho(g) U^* rho(g)^*-1||_2.
```

Then

```text
delta_U(t30)
 <= 2 delta_U(h)+2 delta_U(k)+delta_U(z)+delta_U(b).    (T30-PC3-2)
```

If

```text
E_PC3(U)=2 delta_U(h)^2+2 delta_U(k)^2
          +delta_U(z)^2+delta_U(b)^2,
```

weighted Cauchy--Schwarz and the fact that `t30` is an involution give

```text
x30(U)^2
 =1/2 delta_U(t30)^2
 <=3 E_PC3(U).                                         (T30-PC3-3)
```

There is also a more compressed two-holonomy form.  Put

```text
a=zb.
```

Exact arithmetic gives `|c|=4`, `|a|=2`, and

```text
t30=c^-1 a c.                                          (T30-2HOL-1)
```

Consequently, for

```text
E_2HOL(U)=2 delta_U(c)^2+delta_U(a)^2,
```

one has

```text
delta_U(t30)<=2delta_U(c)+delta_U(a),
x30(U)^2<=(3/2)E_2HOL(U).                              (T30-2HOL-2)
```

The two coordinates are geometrically intrinsic: `c=hk` crosses between the
two packet `S3` components inside the rank-three core, while `a=zb` is the
reflection in the collision--central-`C3` cell `<z,b> ~= S3`.

The exact audit additionally computes

```text
|P|=1344,
|P intersect zPz^-1|=96,
|PzP|=18816,
GL_4(F2)=P disjoint_union PzP.
```

Hence this is not an accidental word identity: `z` crosses the unique
nontrivial parabolic double coset, and `(T30-PC3-1)` selects the transverse
transvection needed by the q14 wall.

