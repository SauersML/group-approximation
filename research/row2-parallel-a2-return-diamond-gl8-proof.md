---
rg: 2
id: row2-parallel-a2-return-diamond-gl8-proof
kind: route
title: Compare both literal a2 paths inside the marked-center GL8 chart
target: row2-parallel-a2-return-diamond-has-gl8-model
requires:
  - row2-marked-center-action-return-has-gl8-model
  - outer-root-leavitt-table
---

The coefficient equality `s_1t_00=a_2` gives

```text
[x_57(s_1),x_78(t_00)]=x_58(a_2)=A_2.                 (1)
```

Conjugation by `P=w_65(1)` changes root index `5` to `6`, so `(1)` becomes

```text
[x_67(s_1),x_78(t_00)]=x_68(a_2)=R.                   (2)
```

The same coefficient has the second root factorization

```text
[x_69(s_1),x_98(t_00)]=x_68(a_2)=R.                   (3)
```

Finally `Q=w_79(1)` exchanges the two intermediate indices and conjugates
the two factors in `(2)` to the corresponding factors in `(3)`, while
fixing the endpoint root `(6,8)`.

In the preceding `GL_8(F_2)` chart put

```text
x_57(s_1)=e_(10,7_0),       x_78(t_00)=e_(7_0,8_0),
x_67(s_1)=e_(u,7_0),        x_69(s_1)=e_(u,9),
x_98(t_00)=e_(9,8_0),       Q=(7_0 9).                (4)
```

Then `(1)--(3)` are standard length-two transvection paths and `(4)` makes
all three conjugation rows exact.  The previously audited prefix braid,
order-seven heads, marked-center cell and surviving marked child are
unchanged.  The MSI-only audit verifies the entire union and the literal
three-transvection factorizations of both constant Whiteheads.

