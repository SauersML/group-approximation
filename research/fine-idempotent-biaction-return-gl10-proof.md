---
rg: 2
id: fine-idempotent-biaction-return-gl10-proof
kind: route
title: Put the reverse product and both Morita absorption rows in the marked GL10 chart
target: fine-idempotent-biaction-return-has-gl10-model
requires:
  - row2-parallel-a2-return-diamond-has-gl8-model
  - outer-root-leavitt-table
  - rank-deficient-return-row-has-operator-norm-one
---

Prefix cancellation gives

```text
(s_00t_1)(s_1t_00)=s_00t_00=e_00,
e_00s_00=s_00,              t_00e_00=t_00.            (1)
```

The ordinary nonopposite Steinberg commutator law first gives

```text
[x_(8,h)(s_00),x_(h,6)(t_1)]=x_(8,6)(b_2)=B_2.       (2)
```

Conjugate `(2)` by the constant Weyl permutation `K=(8 v)(6 10)`.  Since
`A_2=x_(10,8)(a_2)`, equation `(1)` gives

```text
[K B_2 K^(-1),A_2]
 =[x_(v,10)(b_2),x_(10,8)(a_2)]
 =x_(v,8)(e_00)=D.                                   (3)
```

Let `L=w_(v,8)(1)`.  It exchanges `v,8` and fixes `h,7`, so

```text
Lx_(v,h)(s_00)L^(-1)=x_(8,h)(s_00),
Lx_(7,8)(t_00)L^(-1)=x_(7,v)(t_00).                  (4)
```

Using `(1)` once more, the two composable-root commutators in `(4)` are

```text
[x_(v,8)(e_00),x_(8,h)(s_00)]=x_(v,h)(s_00),
[x_(7,v)(t_00),x_(v,8)(e_00)]=x_(7,8)(t_00).         (5)
```

This proves every asserted Leavitt/Steinberg row.

For the finite model, add vertices `v,h` to the exact eight-vertex model of
`row2-parallel-a2-return-diamond-has-gl8-model` and make the assignments in
`(FIB8)`.  Equations `(2)--(5)` become ordinary transvection path identities.
The MSI-only executable audit checks their union with the coupled prefix
braid, both order-seven heads, the marked-center return, both `a_2` paths,
the constant Weyl factorizations, and survival of the marked child.

