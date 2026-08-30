---
rg: 2
id: stw83-constant-symbol-pullback-proof
kind: route
title: Identify the canonical graph core by its constant corona symbol
target: stw83-canonical-circle-is-constant-symbol-pullback
requires:
  - stw83-circle-connector-canonical-full-corner
---

The concrete model from the prerequisite places `A_N` in
`M(K tensor C(T))` and gives

```text
A_N=C*(S^N tensor 1, K tensor C(T))
   =C*(S^N tensor 1)+K tensor C(T).                      (3)
```

The first summand in (3) lies in `T_N tensor 1`, and the kernel of

```text
q_N tensor id:T_N tensor C(T)->C(T) tensor C(T)
```

is exactly `K tensor C(T)`.  Exactness here is elementary: `C(T)` is
nuclear, so tensoring the Toeplitz extension by `C(T)` preserves its
kernel.  It follows immediately from (3) that every element of `A_N`
has quotient symbol in `C(T) tensor 1`.

Conversely, suppose `x in T_N tensor C(T)` and

```text
(q_N tensor id)(x)=f tensor 1
```

for some `f in C(T)`.  Surjectivity of `q_N` gives a lift
`a in T_N` with `q_N(a)=f`.  Therefore

```text
x-a tensor 1 in ker(q_N tensor id)=K tensor C(T),
```

and both terms on the right belong to the algebra in (3).  Hence
`x in A_N`, proving (1).

Finally, the standard identification
`T_N tensor C(T)=C(T,T_N)` sends `q_N tensor id` to pointwise
application of `q_N`.  Membership of the image in `C(T) tensor 1`
is exactly independence of the coefficient-circle variable, proving (2).
