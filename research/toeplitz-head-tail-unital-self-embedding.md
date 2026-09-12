---
rg: 2
id: toeplitz-head-tail-unital-self-embedding
kind: claim
title: The algebraic Toeplitz ring has an explicit proper unital head-tail self-embedding
distinct_from:
  leavitt-primitive-corner-recursive-extension: that is a nonunital corner embedding inside a group algebra; this is a unital self-embedding of the algebraic Toeplitz ring with an explicit compression left inverse.
  universal-sandwich-ring-is-finitely-presented-and-injective: that universally adjoins a one-sided inverse around one coefficient; this uses the existing Toeplitz relation to manufacture a recursive head-tail decomposition.
---

Let

```text
T=F_2<x,y | yx=1>,                 eps(x)=eps(y)=1,
f=1+xy,                            e_1=x f y.
```

Then

```text
sigma(a)=x a y+eps(a)f                                      (THT1)
```

is an injective unital ring endomorphism of `T`. It has the explicit linear
left inverse

```text
a |-> y a x,                                                (THT2)
```

on its image, is not surjective, and satisfies

```text
sigma(f)=e_1 != 0,       (xy)e_1=e_1,       xy notin sigma(T). (THT3)
```

In the unilateral-shift model of `T`, `sigma(a)` is the block diagonal
operator with scalar head block `eps(a)` and tail block `a`. Thus iteration
gives a literal recursive tape of finite head blocks while retaining a unital
injective coefficient map suitable for an ascending HNN extension.

