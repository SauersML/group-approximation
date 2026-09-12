---
rg: 2
id: literal-prefix-j1-j2-coupling-gl7-proof
kind: route
title: Compile the second native factors from the first and close the adjacent swaps
target: literal-prefix-coupling-of-j1-j2-has-gl7-model
requires:
  - odd-native-s-factor-return-diamond-has-gl7-model
  - native-whitehead-hecke-head-has-order-seven-anchor
  - support-return-charts-meet-in-two-pauli-pairs
  - outer-root-leavitt-table
---

Prefix concatenation in the binary Leavitt algebra gives

```text
s_0(s_00t_0)t_0=s_000t_00,
s_0(s_0t_00)t_0=s_00t_000.                            (1)
```

For the first identity, the compatible paths `9->8->7` and `9->7->8`
give

```text
[x_98(s_0),X_1]=x_97(s_0x_1),
[x_97(s_0x_1),x_78(t_0)]=x_98(s_0x_1t_0)=X_2.        (2)
```

For the second identity, use the paths `7->8->9` and `8->7->9`:

```text
[Y_1,x_89(t_0)]=x_79(y_1t_0),
[x_87(s_0),x_79(y_1t_0)]=x_89(s_0y_1t_0)=Y_2.        (3)
```

These are ordinary nonopposite Steinberg relations and authenticate the
literal second-scale occurrences.  The definitions

```text
J_1=X_1Y_1X_1,       J_2=X_2Y_2X_2                   (4)
```

therefore remove the independent central signs of both actors.

For the finite model, use the first three vertices `(7_0,9,8_0)` of the
existing seven-coordinate chart and put

```text
X_1=e_(8_0,7_0),     Y_1=e_(7_0,8_0),
X_2=e_(9,8_0),       Y_2=e_(8_0,9),

x_98(s_0)=X_2,       x_78(t_0)=Y_1,
x_89(t_0)=Y_2,       x_87(s_0)=X_1.                  (5)
```

Then the intermediate roots in `(2)--(3)` are `e_(9,7_0)` and
`e_(7_0,9)`.  Direct multiplication yields

```text
J_1=(7_0 8_0),       J_2=(8_0 9),
J_1J_2J_1=J_2J_1J_2.                                 (6)
```

All assignments in `(5)` are occurrence assignments on the displayed
finite table.  In particular the proof does not claim that two distinct
coefficient roots have been identified in the full Steinberg group.  The
MSI-only artifact checks `(2)--(6)` and verifies that the marked child on
vertices `(7_1,8_1)` survives.  Hence the literal two-scale prefix packet
has a finite exact `GL_7(F_2)` model and cannot by itself prove the marked
MF obstruction.

