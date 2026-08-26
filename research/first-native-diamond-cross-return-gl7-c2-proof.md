---
rg: 2
id: first-native-diamond-cross-return-gl7-c2-proof
kind: route
title: Attach one native depth-changing diamond to the finite cross-return chart
target: first-native-diamond-extension-of-cross-return-has-gl7-c2-model
requires:
  - private-middle-swap-crosses-returned-morita-branches-but-has-gl6-model
  - reverse-return-has-native-arm-leavitt-diamond
  - outer-root-leavitt-table
---

The ordinary Steinberg commutator law and the two prefix cancellations give

```text
[x_97(t_0),x_76(s_0)]=x_96(t_0s_0)=x_96(1),
[x_98(t_00),x_86(s_00)]=x_96(t_00s_00)=x_96(1).
```

The literal native Whitehead covariance equations are exactly `(RND3)` of
`reverse-return-has-native-arm-leavitt-diamond`.  Since `J_1` is supported
on root coordinates `(7,8)` and `H=w_(9,10)(1)` on `(9,10)`, their root
rectangles are disjoint and they commute.  Conjugating the whole diamond by
`H` proves `(NDC5)` without introducing a new occurrence.

For the finite model, embed the old `GL_6(F_2)` matrices in the upper-left
six coordinates of `GL_7(F_2)`.  With the order `(NDC6)`, the existing arm
`A=V_0` is `e_(9,7_0)`.  Therefore

```text
[e_(9,7_0),e_(7_0,6)]=e_(9,6).
```

Conjugation by the permutation `j_0=(7_0 8_0)` replaces the middle vertex
`7_0` in this path by `8_0`, and the same commutator remains `e_(9,6)`.
The private-middle permutation `H=(9 10)` commutes with `j_0` and fixes the
new vertex `6`, so applying it to both paths verifies the two naturality
rows in `(NDC5)`.

The additional direct factor `C_2=<c>` is central.  Sending
`J` to `(j_0,c)` changes none of the displayed conjugations, commutators,
or involution equations, while it proves that the fixed table has not
identified the external native-Whitehead gauge.  The MSI-only executable
audit `experiments/first_native_diamond_cross_return_gl7_c2_audit.py`
checks the old cross-return equations, the new diamond, its `H` translate,
and survival of `C_1`.  The left regular representation of the generated
finite subgroup supplies the claimed exact marked model.
