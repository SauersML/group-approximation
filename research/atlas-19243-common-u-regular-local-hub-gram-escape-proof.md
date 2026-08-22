---
rg: 2
id: atlas-19243-common-u-regular-local-hub-gram-escape-proof
kind: route
title: Rotate the b eigenspaces only on the K trivial-sign carrier
target: atlas-19243-common-u-regular-local-hub-gram-escape
requires:
  - atlas-19243-has-continuous-regular-s3-line-holonomy
  - atlas-a4-19243-s3xs3-localization
---

As a `K`-representation,

```text
Reg(K x L)
 = (triv + sign + 2 std) tensor C^6.                  (1)
```

The commuting reflection `b in L` acts on each six-dimensional multiplicity
space as three `+1` and three `-1` eigenvalues.  Split `(1)` into the
twelve-dimensional line carrier

```text
E_line=(triv+sign) tensor C^6
```

and the twenty-four-dimensional standard carrier

```text
E_std=2 std tensor C^6.
```

On `E_std`, set `U_theta=1`, so `c_theta=b`.  On `E_line`, pair the six
positive and six negative `b` eigenvectors and put the same real planar
rotation `R_theta` on each pair.  Thus

```text
U_theta=R_theta tensor I_6,
c_theta=U_theta b U_theta^*                            (2)
```

on the line carrier.  This is one unitary on the whole regular local cell,
not merely an abstract choice of a balanced involution.

The collision relation is blockwise exact.  On the line carrier `r=1`, so

```text
r c s c r^-1 c (sr)c=c s c c s c=1
```

for every involution `c`.  On the standard carrier `c=b`; since `b` commutes
with `K`, the collision word is the true local group relation and equals one.
This proves `(A4-LOC-Q)`.

On `E_std`, `V_theta=c_theta b=1`.  On each two-dimensional paired line
block, the product of the two reflections `c_theta b` is rotation through
angle `2 theta`.  Therefore its real trace is `2 cos(2 theta)`, and the trace
of its square is `2 cos(4 theta)`.  Adding the twenty-four identity dimensions
and normalizing by thirty-six gives

```text
Re tau(V_theta)=(24+12 cos(2 theta))/36,
tau(V_theta^2)=(24+12 cos(4 theta))/36,
```

which is `(A4-LOC-GRAM)`.  Finally, unitary energy gives

```text
||V_theta-1||_2^2
 =2-2 Re tau(V_theta)
 =(4/3)sin(theta)^2.
```

Since `K x L` has order thirty-six and is a subgroup of `A8`, restriction of
the left regular representation is `560 Reg(K x L)`.  Repeating the same
construction on every coset block proves the amplified statement.
