---
rg: 2
id: leavitt-d4-l14-n0511-first-carrier-splits-five-ways-proof
kind: route
title: Split the normal 0;511 first carrier by malnormality
target: leavitt-d4-l14-n0511-first-carrier-splits-five-ways
requires:
  - leavitt-d4-l14-six-winner-profile-has-two-classes
---

The common carrier gives `g0=g3=1`.  Put

```text
p=g1, u=g2, v=g4, w=g5, x=g6, y=g7, z=g8, a=g9,
b=g10, c=g11, d=g12, e=g13.
```

The first normal carrier is

```text
H A0=E7^-1 H,
A0=p_3(uv)_2w_3x_2y_3z_2a_3,
E7=(ep)_0.
```

Thus `H A0 H^-1` belongs both to a conjugate of the free factor
`G2*G3` and to `G0`.  Malnormality of complementary free factors gives
`A0=E7=1`, so `ep=1`.  The five maximal noncrossing cancellations of the
alternating seven-syllable word `A0` are

```text
I:   uv=x=z=1,       pwya=1;
II:  uv=y=1,         xz=1, pwa=1;
III: w=z=1,          (uv)x=1, pya=1;
IV:  w=y=1,          (uv)xz=1, pa=1;
V:   x=1,            (uv)z=1, wy=1, pa=1.
```

Every noncrossing cancellation partition refines one of these five, so they
are exhaustive for the remaining carrier and boundary analysis.
