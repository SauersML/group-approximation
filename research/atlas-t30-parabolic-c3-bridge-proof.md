---
rg: 2
id: atlas-t30-parabolic-c3-bridge-proof
kind: route
title: Multiply the packet matrices and telescope the covariance cocycle
target: atlas-t30-is-one-parabolic-c3-bridge
requires:
  - atlas-a4-19243-parabolic-subgroup-ladder
artifacts:
  - experiments/atlas_t30_parabolic_c3_bridge.py
  - experiments/atlas-t30-parabolic-c3-bridge.json
---

The exact script closes

```text
P=<H_6,K,b>
```

and breadth-first enumerates its `1344` elements with words in the displayed
packet/collision generators and their inverses.  For each of the two
nonidentity central elements `z in Z(H_18)`, it solves

```text
t30=p_left z p_right,       p_left,p_right in P.
```

The minimum total parabolic word length is five.  One minimizing solution is

```text
p_left = k_0^-1 h6_2^-1,
p_right= b h6_2 k_0.
```

This is exactly `(T30-PC3-1)`.  The double-coset count follows from

```text
|PzP|=|P|^2/|P intersect zPz^-1|
     =1344^2/96=18816=20160-1344.
```

For the analytic statement, the map `delta_U` obeys

```text
delta_U(g^-1)=delta_U(g),
delta_U(g_1...g_m)<=sum_i delta_U(g_i),
```

by unitary invariance and telescoping.  Apply this to
`k^-1 h^-1 z b h k` to obtain `(T30-PC3-2)`.  With weights
`(2,2,1,1)`, Cauchy--Schwarz gives

```text
(2d_h+2d_k+d_z+d_b)^2
 <=6(2d_h^2+2d_k^2+d_z^2+d_b^2).
```

Finally

```text
delta_U(t30)^2
 =||U rho(t30)U^*-rho(t30)||_2^2
 =2[1-Re tau(U rho(t30)U^*rho(t30))]
 =2x30(U)^2,
```

which proves `(T30-PC3-3)`.

