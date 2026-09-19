---
rg: 2
id: atlas-a4-19243-parabolic-normal-closure-proof
kind: route
title: The affine translation orbit is seven points, while A8 simplicity closes the full chart
target: atlas-a4-19243-parabolic-normal-closure
requires:
  - atlas-a4-19243-parabolic-subgroup-ladder
---

Use the concrete standard affine coordinates supplied by the subgroup ladder.
The repeated first-chart involution in `q_19243` is

```text
b = [ I_3  e_3 ]
    [  0    1  ],
```

so `b` is a nonzero element of the translation radical

```text
V = { [I_3 v; 0 1] : v in F_2^3 } ~= (C2)^3.
```

The linear subgroup `H=GL_3(F2)` normalizes `V` and acts transitively on its
seven nonzero vectors.  Therefore the `H`-conjugacy class of `b` is exactly
`V-{1}`.  These conjugates generate `V`, so

```text
V <= <<b>>_P.
```

Conversely `V` is a normal subgroup of `P=V semidirect H` containing `b`, hence
minimality of normal closure gives

```text
<<b>>_P <= V.
```

Thus equality holds.  Quotienting the affine semidirect product by `V` leaves
its linear part `H`, proving `(19243-P-NC)` and `(19243-P-QUOT)`.

For the full chart, `b` is nonidentity in `A8`.  The alternating group `A8` is
simple, so the normal closure of any nonidentity element is all of `A8`.
Therefore

```text
<<b>>_A8=A8.
```

The accompanying exact `F2` audit independently reconstructs the fourteen-word
core and `q_19243`, verifies the seven-element `H`-orbit of `b`, obtains normal
closure orders `8` and `20160` in `P` and `A8`, and checks that the parabolic
quotient has order `168`.
