---
rg: 2
id: leavitt-degree4-abstract-tietze-proof
kind: route
title: Pivot on H z and eliminate K L M once each
target: leavitt-degree4-abstract-tietze-preserves-d
requires:
  - leavitt-degree-four-corner-subgroup-is-v4-d8-f4
---

Use the cyclic corner names

```text
H=r0|e1|a2|c1|b3|d2|p3,
K=e0|a1|c0|b2|d1|p2|r3,
L=p0|r1|e2|a3|c2,
M=b1|d0|p1|r2|e3,
a=a0, b=b0, c=c3, d=d3.
```

The four exact Reidemeister--Schreier relators, cyclically based at a
`z`-occurrence, are

```text
H z,
z b z^(-1) d z L,
z a z^(-1) c z M,
z K.                                                   (TP1)
```

Thus the abstract corner quotient is

```text
P=<D*F(H,K,L,M),z | (TP1)>.
```

The first relation gives `z=H^(-1)`.  The last then gives `K=H`, and the
middle two give, using that `a,b,c,d` are involutions,

```text
L=H d H^(-1)b H,
M=H c H^(-1)a H.                                     (TP2)
```

Each of `K,L,M` was a distinct free generator and occurs as the left side of
exactly one equation in `(TP2)`.  Tietze elimination therefore leaves no
relation on `D` or `H`:

```text
P = D*<H>.                                            (TP3)
```

The induced map fixes `D`, so it is injective there.  Since
`<c,d>=D8` and `(cd)^2=[c,d]` is its central involution, the intended target
survives `(TP3)`.
