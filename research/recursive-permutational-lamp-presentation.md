---
rg: 2
id: recursive-permutational-lamp-presentation
kind: claim
title: A recursively enumerable point stabilizer gives a finitely generated recursive lamp presentation
distinct_from:
  augmentation-lamp-finite-presentation-criterion: that asks for finite generation of stabilizers and finitely many double cosets to obtain a finite presentation; this needs only recursive enumerability and obtains a recursive presentation.
  direct-sharp-actor-wreath-forces-actor-fp: that is a finite-presentation obstruction; it does not obstruct the recursive presentation proved here.
---

ESTABLISHED.

Let

```text
A=<S | R>
```

be finitely generated and recursively presented, let `A` act transitively on
`X`, fix `x in X`, and suppose the preimage in the free group `F(S)` of the
point stabilizer `A_x` is recursively enumerable.  Then the binary
permutational wreath product

```text
W=(direct_sum_X C_2) rtimes A
```

is finitely generated and recursively presented.

Choose one root lamp `c` at `x`.  A recursive presentation is

```text
< S,c |
    R,
    c^2=1,
    [c,h]=1                  (h in the enumerated preimage of A_x),
    [c,g c g^-1]=1           (g in F(S)) >.                 (RPL1)
```

The relators are recursively enumerable.  The stabilizer relations say that
the conjugate lamp `g c g^-1` depends only on `g x`; the last family says that
all site lamps commute.  Conversely these impose exactly the elementary
abelian direct-sum base and its permutation covariance, so `(RPL1)` presents
`W`.  Transitivity makes `S union {c}` a finite generating set.

There is a particularly useful specialization.  Suppose `X` is the conjugacy
class of a named involution `i in A`.  Then

```text
A_x=C_A(i).
```

For a recursively presented `A`, its preimage is recursively enumerable:
enumerate proofs from `R` of the equalities `[h,i]=1`.  No decision procedure
for the word problem and no finite generation of the centralizer is required.

Fix a named word `t` with `t i t^-1 != i` and put

```text
m_0 = c (t c t^-1).
```

Adjoining involutions `z,J`, the finitely many relations making `J` central
on the finite generating set, and

```text
[m_0,z]=J                                               (RPL2)
```

again gives a finitely generated recursively presented marked group.  Thus a
recursively presented sharply 2-transitive actor is already sufficient for
the exact two-point lamp/D8 construction; finite presentation of the actor
and finite generation of a point stabilizer are not needed before the
normalized-HS argument.
