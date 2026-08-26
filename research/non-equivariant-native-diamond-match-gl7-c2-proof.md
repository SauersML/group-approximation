---
rg: 2
id: non-equivariant-native-diamond-match-gl7-c2-proof
kind: route
title: Match both primed native arms without transporting both factors by J
target: non-equivariant-native-diamond-arm-matches-retain-gl7-c2-gauge
requires:
  - first-native-diamond-extension-of-cross-return-has-gl7-c2-model
  - reverse-return-has-native-arm-leavitt-diamond
  - reverse-mixed-root-has-two-positive-hecke-commutator-returns
  - outer-root-leavitt-table
---

For ordinary compatible Steinberg roots,

```text
[x_ij(a),x_jk(b)]=x_ik(ab).
```

Apply this first to the paths `9->7->8` and `8->7->6`.  Prefix
concatenation in the binary Leavitt algebra gives

```text
t_0t_0=t_00,                    s_0s_0=s_00,
```

and hence

```text
[x_97(t_0),x_78(t_0)]=x_98(t_00),
[x_87(s_0),x_76(s_0)]=x_86(s_00).                     (1)
```

For the genuinely cross-row match, the established second native diamond
contains

```text
C_2=[x_25(t_1),A_2]=x_28(t_00),
D_2=x_87(s_00),
```

and the independent positive return contains `h_1=x_76(1)`.  Therefore the
paths `9->2->8` and `8->7->6` give

```text
[x_92(1),C_2]=x_98(t_00),
[D_2,h_1]=x_86(s_00).                                 (2)
```

Neither calculation in `(1)--(2)` invokes `J_1`.

For the finite model, retain every matrix in the existing
`GL_7(F_2) times C_2` packet.  With the vertex order used there, assign the
new occurrences by `(NDM4)`.  The four commutators are the two elementary
path products in `(NDM5)`.  No opposite-root commutator is introduced.

The `C_2` coordinate of `J_1=(j_0,c)` occurs only in the old expressions
`J_1AJ_1^(-1)` and `J_1BJ_1^(-1)`, so it has even parity in the complete
table.  Every new occurrence has zero `C_2` coordinate.  Thus all new rows
are compatible with arbitrary `c`, proving that the non-equivariant matches
do not kill the gauge.  The MSI-only executable audit checks the complete
matrix extension and survival of the old marked child.
