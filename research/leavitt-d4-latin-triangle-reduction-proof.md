---
rg: 2
id: leavitt-d4-latin-triangle-reduction-proof
kind: route
title: Solve all carrier matches and retain the cyclic Latin boundary
target: leavitt-d4-latin-triangle-reduction
requires:
  - leavitt-d4-direct-flux-fence
  - leavitt-repeated-long-corner-template-kills-omega
---

For each post-pivot residual write

```text
Ri=H Ai H^-1 Bi H^-1 Ci.
```

Introduce carrier words `P,Q,R` and coefficient arcs `A,B,C`, and assign

```text
R0=P A Q,          R1=Q^-1 B R,          R2=R^-1 C P^-1.
```

Equivalently, the three corner triples are

```text
(H^-1P,    H A,    H Q),
(H^-1Q^-1, H B,    H R),
(H^-1R^-1, H C,    H P^-1).
```

Eliminating `Q,R` from the three relators gives
`P(ABC)P^-1=1`.  For the actual cyclic corners, all carrier-matching
equations hold identically after setting

```text
g0=g3=1,     g2=g8^-1, g4=g8,
g1=g9^-1,    g5=g9,
```

with `g6,g7,g8,g9` arbitrary.  Put

```text
a=g6, b=g7, c=g8, d=g9.
```

Then

```text
H  =b_0 c_1 d_2 a_3,
B0 =a_0 b_1 c_2 d_3,
B1 =d_0 a_1 b_2 c_3,
B2 =c_0 d_1 a_2 b_3,
```

and `ABC` is exactly

```text
F=H^-1 B0 H^-1 B1 H^-1 B2.                              (1)
```

The four copy projections of `(1)` are

```text
E0=b^-1 a b^-1 d b^-1 c,
E1=c^-1 b c^-1 a c^-1 d,
E2=d^-1 c d^-1 b d^-1 a,
E3=a^-1 d a^-1 c a^-1 b.                               (2)
```

For target copy 0, `E1=1` solves

```text
d=c a^-1 c b^-1 c.                                      (3)
```

Hence the coefficient search is intrinsically three-parameter: check
`E2=E3=1`, `E0=h`, and finally the full free-product equality `F=h_0`.
The attached exact script implements `(1)`--`(2)` in the faithful twenty-leaf
Bergman chart.  The twelve-element calibration tested 20,736 quadruples and
had no projection survivor.  The four-parameter reduction itself is exact
and unrestricted.
