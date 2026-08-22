---
rg: 2
id: leavitt-d4-balanced-rank9-triangles-are-fenced-proof
kind: route
title: Split the common five-syllable carrier and fence both rank-nine classes
target: leavitt-d4-balanced-rank9-triangles-are-fenced
requires:
  - degree4-cyclic-orbit-valence-parity
---

Use the exact corners

```text
H=g9_0 g10_1 g11_2 g0_3 g1_2 g2_1 g3_0 g4_1 g5_0 g6_1 g7_2 g8_3,
A1=g2_3 g3_2 g4_3 g5_2 g6_3.
```

The common carrier equation is `H^-1 C0=A1^-1H^-1`.  Free-factor normal
form first forces `g0=1` and then `A1=1`.  The alternating five-syllable word
has exactly two branches:

```text
I:  g3=g5=1, g6=(g2 g4)^-1;
II: g4=1, g5=g3^-1, g6=g2^-1.
```

Write `p=g1,u=g2,a=g7,b=g8,c=g9,d=g10,e=g11`; in branch II also write
`x=g3`, and in branch I put `v=g4`.

For class A, the remaining equations are

```text
H A0=E1^-1H^-1,       H^-1C1=E2^-1H,
K=H^-1B0 H^-1B1 H E3 H^-1E4 H^-1E5.
```

In branch I, `H=c0d1(epa)2b3` and `A0=(pa)3`.  The first equation forces
`c=d=1`, `epa=1`, and `pa=b^-2`.  The second becomes

```text
b^-1_3 (ep)_0 b^-1_3 v_0=1.
```

If `b=1`, then `ep=v^-1` and direct substitution gives `K=1`.  Otherwise
`ep=v=1`, `b^2=1`, and

```text
K=b_3 b_0 b_3 b_1 u^-1_0 b_2 b_3 u_0.
```

The unique copy-two syllable `b_2` must survive, while its right tail
`b_3u_0` cannot vanish, so this is not one-copy.  In branch II the equations
give

```text
c=d=a=1, e=p^-1, b^2=1, x=b p^-1 b,
K=b_3 b_0 (p^-1b)_3 b_1 p_3 u^-1_0 b_2 b_3 u_0.
```

Again `b=1` gives `K=1`; for `b!=1` the same unique-copy-two/right-tail
argument fences `K`.

For class B, the first carrier equation has the same reductions (with `E3`
in place of `E1`).  In branch I the final equation is

```text
b^-1_3(ep)_0 b^-1_3(uv)^-1_0 a_1 b_2 b^-1_3(ep)_1u_0=1.
```

Its unique `b_2` forces `b=1`; normal form then gives
`a=p^-1,e=1,p=v`, and the boundary is `K=1`.  In branch II the corresponding
equation is

```text
b^-1_3(ep)_0 b^-1_3u^-1_0 a_1 b_2 b^-1_3(ep)_1u_0=1.
```

It again forces `b=1`, followed by `a=1,e=p^-1,x=p`, and again `K=1`.
These four branches exhaust both NNN classes.  Global inversion gives the six
III orientations, completing all twelve balanced rank-nine systems.
