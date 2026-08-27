---
rg: 2
id: depth-two-a3-external-return-proof
kind: route
title: Evaluate the asymmetric A3 path before typing its returned occurrence
target: depth-two-a3-return-is-gauged-external-root
requires:
  - one-singer-square-does-not-identify-external-return-gauge
  - native-weyl-return-gauges-have-s3-model
---

Prefix cancellation gives

```text
t_00(s_00t_01)=t_01,
(s_00t_01)s_01=s_00,
t_01s_01=1,
t_00s_01=0,                                           (AERP1)
```

which proves `(AER1)`.  The first bracketing is

```text
[A,B]=x_(7,11)(t_01),
[[A,B],C]=x_78(t_01s_01)=x_78(1).                     (AERP2)
```

The second is

```text
[B,C]=x_(10,8)(s_00),
[A,[B,C]]=x_78(t_00s_00)=x_78(1).                     (AERP3)
```

Finally `[A,G]=x_78(t_00s_01)=1`, proving `(AER3)`.

Equation `(AER4)` is an equality of full group words, so restriction to any
representation and reducing signed-Hecke carrier gives `(AER5)` without a
choice of factorization.  Multiplication by the Whitehead occurrence adds
its reservoir factor `D`, yielding `DE`.  The exact output conjugacy square
has the same calculation as the already established external-return Singer
square and yields `(AER7)`.

The two reflections in `(AER8)` obey the existing native Weyl/Singer gauge
relations and have nontrivial order-three product.  Since none of the four
private positive-root letters is a signed-carrier endomorphism, `(AER3)`
does not add a compressed gauge equation to this assignment.  This proves
the stated interface fence.
